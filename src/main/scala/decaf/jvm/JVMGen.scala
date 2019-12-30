package decaf.jvm

import decaf.driver.{Config, Phase}
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.tree.TreeNode.{ArithOp, EqOrCmpOp}
import decaf.frontend.tree.TypedTree._
import decaf.frontend.tree.{TreeNode, TypedTree}
import decaf.lowlevel.StringUtils
import org.objectweb.asm.{ClassWriter, Label, MethodVisitor, Opcodes}

import scala.collection.mutable

class JVMGen(implicit config: Config)
    extends Phase[Tree, List[JVMClass]]("jvm", config)
    with Util {

  /**
    * Transformer entry.
    *
    * @param input a typed abstract syntax tree
    * @return a possibly collection of JVM classes
    */
  override def transform(input: Tree): List[JVMClass] = {
    val inputsEmit = input.classes.map(emitClass)

    // printf("===== Emitted all classes. ========\n")

    // printf(s"funcionTypes = ${functionTypes.toList}\n")

    val functionBasesEmit = functionTypes.toList.map(emitFunctionBase)

    // printf("====== Emitted all function base classes =========\n")

    val assistMethodsEmit =
      assistMethods.toList.map(x => emitAssistMethod(x._1, x._2))

    // printf("======= Emitted all assist methods ===========\n")

    // The order, I guess, is nothing
    inputsEmit ++ functionBasesEmit ++ assistMethodsEmit ++ lambdaJVMClasses.toList
  }

  /**
    * After generating JVM classes, dump them to binary files.
    *
    * @param classes JVM classes
    */
  override def onSucceed(classes: List[JVMClass]): Unit = {
    classes.foreach { _.writeFile(config.dstDir) }
  }

  /**
    * Generate bytecode for a decaf class.
    *
    * @param clazz the class
    * @return the wrapped class file
    */
  def emitClass(clazz: ClassDef): JVMClass = {
    implicit val cw = new ClassWriter(
      ClassWriter.COMPUTE_FRAMES + ClassWriter.COMPUTE_MAXS
    )

    // As said in https://docs.oracle.com/javase/specs/jvms/se9/html/jvms-4.html#jvms-4.1-200-E.1:
    //   In Java SE 8 and above, the Java Virtual Machine considers the ACC_SUPER flag to be set in every class file,
    //   regardless of the actual value of the flag in the class file and the version of the class file.
    // Thus, we always set on ACC_SUPER flag and let a non-inherited decaf class extend java.lang.Object.
    val access = Opcodes.ACC_PUBLIC + Opcodes.ACC_SUPER + (if (clazz.isAbstract)
                                                             Opcodes.ACC_ABSTRACT
                                                           else 0)
    val superClass =
      clazz.parent.map(internalName).getOrElse(JAVA_SUPER_INTERNAL_NAME)
    cw.visit(Opcodes.V1_8, access, clazz.name, null, superClass, null)

    // 简单来说，Decaf 没有构造方法，这个默认构造方法其实什么也没做
    // First add the default constructor:
    val mv = cw.visitMethod(
      Opcodes.ACC_PUBLIC,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      null,
      null
    )
    mv.visitCode()
    mv.visitVarInsn(Opcodes.ALOAD, 0) // 把 this 压到操作数栈里，是为了调用父类的构造函数
    mv.visitMethodInsn(
      Opcodes.INVOKESPECIAL,
      superClass,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      false
    ) // call super
    mv.visitInsn(Opcodes.RETURN)
    mv.visitMaxs(-1, -1) // pass in random numbers, as COMPUTE_MAXS flag enables the computation
    mv.visitEnd()

    // Then generate every user-defined member:
    clazz.fields.foreach {
      case field: VarDef =>
        cw.visitField(
          Opcodes.ACC_PUBLIC,
          field.name,
          descriptor(field.symbol.typ),
          null,
          null
        )
      case method: MethodDef =>
        // printf(s"method = $method, ")
        // printf(s"method.symbol = ${method.symbol}, ")
        // printf(s"method.symbol.typ = ${method.symbol.typ}, ")
        // printf(s"\n")

        functionTypes += method.symbol.typ
        assistMethods += new Tuple2(clazz, method)

        emitMethod(clazz, method)
    }
    cw.visitEnd()

    JVMClass(clazz.name, cw.toByteArray)
  }

  /**
    * 为每一个 method 声明一个辅助函数类
    *
    * @param clazz the class
    * @return the wrapped class file
    */
  def emitAssistMethod(clazz: ClassDef, method: MethodDef): JVMClass = {
    val assistName = clazz.name + "$" + method.name
    val parentType = fromFunTypeToFunBaseClassType(method.symbol.typ)
    val assistType = ClassType(assistName, Some(parentType))

    // printf(s"emitAssitsMethod: assistName = $assistName\n")

    implicit val cw = new ClassWriter(
      ClassWriter.COMPUTE_FRAMES + ClassWriter.COMPUTE_MAXS
    )
    val superClass = internalName(parentType)
    cw.visit(
      Opcodes.V1_8,
      Opcodes.ACC_PUBLIC + Opcodes.ACC_SUPER,
      assistName,
      null,
      superClass,
      null
    )

    if (!method.isStatic) {
      // 对于成员方法，类里面需要捕获一个[[self]]
      cw.visitField(
        Opcodes.ACC_PUBLIC,
        "self",
        descriptor(clazz.symbol.typ),
        null,
        null
      )
    } else {
      // 对于静态方法，类里面什么都没有。
    }

    // First add the default constructor:
    val construct_mv = cw.visitMethod(
      Opcodes.ACC_PUBLIC,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      null,
      null
    )
    construct_mv.visitCode()
    construct_mv.visitVarInsn(Opcodes.ALOAD, 0)
    construct_mv.visitMethodInsn(
      Opcodes.INVOKESPECIAL,
      superClass,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      false
    ) // call super
    construct_mv.visitInsn(Opcodes.RETURN)
    construct_mv.visitMaxs(-1, -1) // pass in random numbers, as COMPUTE_MAXS flag enables the computation
    construct_mv.visitEnd()

    // 定义一个apply
    // apply 的类型是和 method 完全一样的
    implicit val apply_mv =
      cw.visitMethod(
        Opcodes.ACC_PUBLIC,
        "apply",
        method_descriptor(method.symbol.typ),
        null,
        null
      )
    implicit val apply_ctx = new Context(assistType, false)
    // apply 的参数和原本 method 的参数完全一致
    method.params.foreach { p =>
      apply_ctx.declare(p.symbol)
    }

    apply_mv.visitCode()
    if (!method.isStatic) {
      // 把当前栈帧中 0 号位置的局部变量（即 this）压入操作数栈
      apply_mv.visitVarInsn(Opcodes.ALOAD, 0)
      // 得到 this.self
      apply_mv.visitFieldInsn(
        Opcodes.GETFIELD,
        internalName(assistType),
        "self",
        descriptor(clazz.symbol.typ)
      )

      // self 已在操作数栈顶，无需再次压栈
      // 把所有参数依次压入操作数栈
      method.params.foreach { p =>
        apply_mv.visitVarInsn(loadOp(p.symbol.typ), apply_ctx.index(p.symbol))
      }

      // 调用 method
      // 虽然之前的框架中最后一个参数传了false，但正如asm的文档和代码锁表明的，这个false的传递并无必要
      apply_mv.visitMethodInsn(
        Opcodes.INVOKEVIRTUAL,
        internalName(clazz.symbol),
        method.name,
        method_descriptor(method.symbol.typ)
      )
    } else {
      // 把所有参数依次压入操作数栈
      method.params.foreach { p =>
        apply_mv.visitVarInsn(loadOp(p.symbol.typ), apply_ctx.index(p.symbol))
      }

      // 调用 method
      apply_mv.visitMethodInsn(
        Opcodes.INVOKESTATIC,
        internalName(clazz.symbol),
        method.name,
        method_descriptor(method.symbol.typ)
      )
    }
    // return
    if (!method.symbol.typ.ret.isVoidType) {
      apply_mv.visitInsn(returnOp(method.symbol.typ.ret))
    } else {
      apply_mv.visitInsn(Opcodes.RETURN)
    }
    apply_mv.visitMaxs(-1, -1)
    apply_mv.visitEnd()

    // Q: 也许我需要把这个类以某种方式保存下来，否则我该怎么生成这个类的对象呢？
    // A: 观察之后的 NewClass() 可知，新建对象时 JVM 可以根据类的名称来找到这个类。

    JVMClass(assistName, cw.toByteArray)
  }

  /**
    * 为每一个 lambda 表达式声明一个lambda函数类
    * 这里假定所有的 lambda 表达式都已被转为 BlockLambda
    *
    * @param lambda the block lambda
    * @return the wrapped class file
    */
  def emitLambda(
      lambda: BlockLambda,
      index: Int,
      classType: ClassType,
      isStatic: Boolean
  ): Unit = {
    // printf(
    //   s"emitLambda(lambda = $lambda, index = $index, classType = $classType, isStatic = $isStatic)\n"
    // )

    // 声明一个函数类
    val lambdaName = "Lambda$" + index
    val parentType = fromFunTypeToFunBaseClassType(
      lambda.typ.asInstanceOf[FunType]
    )
    val lambdaType = ClassType(lambdaName, Some(parentType))

    implicit val cw = new ClassWriter(
      ClassWriter.COMPUTE_FRAMES + ClassWriter.COMPUTE_MAXS
    )
    val superClass = internalName(parentType)
    cw.visit(
      Opcodes.V1_8,
      Opcodes.ACC_PUBLIC + Opcodes.ACC_SUPER,
      lambdaName,
      null,
      superClass,
      null
    )

    // 为 this 创建成员变量
    // 方便起见，这里都有定义，但如果 lambda 在静态方法中，[[self]]不会被赋值
    cw.visitField(
      Opcodes.ACC_PUBLIC,
      "_self", // a prepended underscore to distinguish it from a ordinary [[self]]
      descriptor(classType),
      null,
      null
    )
    // 为捕获变量创建成员变量
    lambda.scope.captured.map(
      v =>
        cw.visitField(
          Opcodes.ACC_PUBLIC,
          v.name,
          descriptor(v.typ),
          null,
          null
        )
    )

    // First add the default constructor
    val construct_mv = cw.visitMethod(
      Opcodes.ACC_PUBLIC,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      null,
      null
    )
    construct_mv.visitCode()
    construct_mv.visitVarInsn(Opcodes.ALOAD, 0)
    construct_mv.visitMethodInsn(
      Opcodes.INVOKESPECIAL,
      superClass,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      false
    ) // call super
    construct_mv.visitInsn(Opcodes.RETURN)
    construct_mv.visitMaxs(-1, -1) // pass in random numbers, as COMPUTE_MAXS flag enables the computation
    construct_mv.visitEnd()

    // 定义一个apply
    implicit val apply_mv =
      cw.visitMethod(
        Opcodes.ACC_PUBLIC,
        "apply",
        method_descriptor(lambda.typ),
        null,
        null
      )
    implicit val apply_ctx = new Context(classType, isStatic)
    // 这里有一些歧义，虽然 lambda 表达式是在一个静态方法里，不会有 this 的传递
    // 但 lambda 表达式本身在这里的设计中还是作为一个成员方法来调用的。
    // 此处 isStatic 表示的含义在原有框架中和被我魔改过的框架中已经不同了。
    // 现在 isStatic 仅仅代表最外层的函数体是否是静态的，所以用它来判断是否有第0个参数传入已经不再合理了。
    apply_ctx.next = 1
    // apply 的参数和 params 完全一致
    lambda.params.foreach { p =>
      apply_ctx.declare(p.symbol)
    }

    apply_mv.visitCode()

    // 此时，函数对象被放到了 0 号位置
    // 先把函数对象从 0 号位置取出来
    apply_mv.visitVarInsn(Opcodes.ALOAD, 0)
    if (!isStatic) {
      // 如果不在 static中的话，需要捕获
      apply_mv.visitInsn(Opcodes.DUP)
      apply_mv.visitFieldInsn(
        Opcodes.GETFIELD,
        internalName(lambdaType),
        "_self",
        descriptor(classType)
      )
      apply_mv.visitVarInsn(storeOp(classType), 0)
    }
    // 把其他的捕获变量加进去
    lambda.scope.captured.map(p => {
      apply_ctx.declare(p)

      apply_mv.visitInsn(Opcodes.DUP)
      apply_mv.visitFieldInsn(
        Opcodes.GETFIELD,
        internalName(lambdaType),
        p.name,
        descriptor(p.typ)
      )

      apply_mv.visitVarInsn(storeOp(p.typ), apply_ctx.index(p))
    })
    apply_mv.visitInsn(Opcodes.POP)

    // 去搞函数体
    implicit val loopExits: List[Label] = Nil
    emitStmt(lambda.block)

    if (lambda.typ.asInstanceOf[FunType].ret.isVoidType) {
      // 其实我应该是可以无脑加一个return的
      apply_mv.visitInsn(Opcodes.RETURN)
    }

    apply_mv.visitMaxs(-1, -1)
    apply_mv.visitEnd()

    lambdaJVMClasses += JVMClass(lambdaName, cw.toByteArray)
  }

  /**
    * 声明已有函数对象所需的基类
    *
    * @param typ function type of the base class
    * @return the wrapped class file
    */
  def emitFunctionBase(typ: FunType): JVMClass = {
    // 在函数基类中，
    // 没有成员变量
    // 有且仅有一个成员方法 apply，apply中什么都没有，直接根据需要返回0/null或直接return。
    val className = fromFunTypeToFunBaseClassName(typ)
    val classType = ClassType(className, None)

    implicit val cw = new ClassWriter(
      ClassWriter.COMPUTE_FRAMES + ClassWriter.COMPUTE_MAXS
    )
    val superClass = JAVA_SUPER_INTERNAL_NAME
    cw.visit(
      Opcodes.V1_8,
      Opcodes.ACC_PUBLIC + Opcodes.ACC_SUPER,
      className,
      null,
      superClass,
      null
    )

    // First add the default constructor:
    val construct_mv = cw.visitMethod(
      Opcodes.ACC_PUBLIC,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      null,
      null
    )
    construct_mv.visitCode()
    construct_mv.visitVarInsn(Opcodes.ALOAD, 0)
    construct_mv.visitMethodInsn(
      Opcodes.INVOKESPECIAL,
      superClass,
      CONSTRUCTOR_NAME,
      CONSTRUCTOR_DESC,
      false
    ) // call super
    construct_mv.visitInsn(Opcodes.RETURN)
    construct_mv.visitMaxs(-1, -1) // pass in random numbers, as COMPUTE_MAXS flag enables the computation
    construct_mv.visitEnd()

    // 定义一个 apply，其类型即为 typ
    implicit val apply_mv =
      cw.visitMethod(
        Opcodes.ACC_PUBLIC,
        "apply",
        method_descriptor(typ),
        null,
        null
      )
    implicit val apply_ctx = new Context(classType, false)

    apply_mv.visitCode()
    if (!typ.ret.isVoidType) {
      // 这里其实没有意义，但不知道为什么，我不能传一个空引用……
      typ.ret match {
        case IntType | BoolType =>
          apply_mv.visitLdcInsn(0)
          apply_mv.visitInsn(Opcodes.IRETURN)
        case t @ FunType(_, _) =>
          apply_mv.visitTypeInsn(Opcodes.NEW, toASMType(t).getInternalName)
          apply_mv.visitInsn(Opcodes.DUP)
          apply_mv.visitMethodInsn(
            Opcodes.INVOKESPECIAL,
            toASMType(t).getInternalName,
            CONSTRUCTOR_NAME,
            CONSTRUCTOR_DESC,
            false
          )
          apply_mv.visitInsn(Opcodes.ARETURN)
        case t @ ClassType(_, _) =>
          apply_mv.visitTypeInsn(Opcodes.NEW, internalName(t))
          apply_mv.visitInsn(Opcodes.DUP)
          apply_mv.visitMethodInsn(
            Opcodes.INVOKESPECIAL,
            internalName(t),
            CONSTRUCTOR_NAME,
            CONSTRUCTOR_DESC,
            false
          )
          apply_mv.visitInsn(Opcodes.ARETURN)
        case StringType =>
          apply_mv.visitLdcInsn("")
          apply_mv.visitInsn(Opcodes.ARETURN)
        // TODO: 还有一些其他情况需要考虑……
      }
    } else {
      apply_mv.visitInsn(Opcodes.RETURN)
    }
    apply_mv.visitMaxs(-1, -1)
    apply_mv.visitEnd()

    JVMClass(className, cw.toByteArray)
  }

  /**
    * Emit bytecode for a method. Code will be appended to the class writer.
    *
    * @param method the method
    * @param cw     the current class writer
    */
  def emitMethod(clazz: ClassDef, method: MethodDef)(
      implicit cw: ClassWriter
  ): Unit = {
    // printf(s"emitMethod(method = $method)\n")

    // Methods are always public, but they can be static or not.
    val access = Opcodes.ACC_PUBLIC + (if (method.isStatic) Opcodes.ACC_STATIC
                                       else 0) + (if (method.isAbstract)
                                                    Opcodes.ACC_ABSTRACT
                                                  else 0)
    val desc =
      if (method.symbol.isMain) MAIN_DESCRIPTOR
      else method_descriptor(method.symbol.typ)
    implicit val mv = cw.visitMethod(access, method.name, desc, null, null)

    // Allocate indexes (in JVM local variable array) for every argument. For member methods, index 0 is reserved for
    // `this`.
    implicit val ctx = new Context(clazz.symbol.typ, method.isStatic)
    method.params.foreach { p =>
      ctx.declare(p.symbol)
    }

    if (!method.isAbstract) {
      // Visit method body and emit bytecode.
      mv.visitCode()
      implicit val loopExits: List[Label] = Nil
      emitStmt(method.body)

      //   printf(">>> Emitted a body of a method.\n")

      appendReturnIfNecessary(method)
      mv.visitMaxs(-1, -1) // again, random arguments
      mv.visitEnd()
    }
  }

  /**
    * JVM requires every method to have explicit RETURN instruction for every execution path. For methods that actually
    * returns a value, our compiler frontend should ensure this. However, a decaf program may omit redundant return
    * statements in a method that returns nothing (or, returns void). In these conditions, we shall insert a RETURN
    * instruction at the end, if not any.
    *
    * @param methodDef the method
    * @param mv        the current method visitor
    */
  def appendReturnIfNecessary(
      methodDef: MethodDef
  )(implicit mv: MethodVisitor): Unit = {
    if (!methodDef.returnType.typ.isVoidType) return

    val stmts = methodDef.body.stmts
    if (stmts.isEmpty || !stmts.last.isInstanceOf[Return])
      mv.visitInsn(Opcodes.RETURN)
  }

  type LocalVars = mutable.TreeMap[LocalVarSymbol, Int]

  private class Context(
      val currentClassType: ClassType,
      val isStatic: Boolean = true
  ) {
    val index: LocalVars = new LocalVars

    def declare(v: LocalVarSymbol): Int = {
      index(v) = next
      val retIndex = next
      next += 1
      retIndex
    }

    var next: Int = if (isStatic) 0 else 1
  }

  /**
    * Emit bytecode for a statement. Code will be appended to the method writer.
    *
    * @param stmt      the statement
    * @param mv        the current method writers
    * @param loopExits exit labels for the entered loops so far, arranged from the inner most to the outer most
    * @param ctx       the current context
    */
  def emitStmt(
      stmt: Stmt
  )(implicit mv: MethodVisitor, loopExits: List[Label], ctx: Context): Unit = {
    // printf(s"At ${stmt.pos}, emitStmt(stmt = $stmt)\n")

    stmt match {
      case Block(stmts) => stmts foreach emitStmt

      case v: LocalVarDef =>
        // JVM will complain if a local variable is read but not initialized yet. It also seems that when the local
        // variable is firstly initialized in a more inner scope rather than the outer most local scope, JVM reports
        // an error. To avoid these, let's simply initialize every user-defined local variable right now, in case
        // the user didn't.
        val index = ctx.declare(v.symbol)
        v.init match {
          case Some(expr) => emitExpr(expr)
          case None       => loadDefaultValue(v.typeLit.typ)
        }
        mv.visitVarInsn(storeOp(v.typeLit.typ), index)

      case Assign(LocalVar(v), rhs) =>
        emitExpr(rhs)
        mv.visitVarInsn(storeOp(v.typ), ctx.index(v))

      case Assign(MemberVar(receiver, v), rhs) =>
        emitExpr(receiver)
        emitExpr(rhs)
        mv.visitFieldInsn(
          Opcodes.PUTFIELD,
          internalName(v.owner),
          v.name,
          descriptor(v.typ)
        )

      case Assign(IndexSel(array, index), rhs) =>
        emitExpr(array)
        emitExpr(index)
        emitExpr(rhs)
        val elemType = array.typ.asInstanceOf[ArrayType].elemType
        mv.visitInsn(arrayStoreOp(elemType))

      case ExprEval(expr) => emitExpr(expr)
      case Skip()         => // nop

      case If(cond, trueBranch, falseBranch) =>
        emitExpr(cond)
        ifThenElse(
          emitStmt(trueBranch),
          emitStmt(falseBranch.getOrElse(TypedTree.Block()(null)))
        )
      case While(cond, body) =>
        val exit = new Label
        loop(emitExpr(cond), exit) {
          emitStmt(body)(mv, exit :: loopExits, ctx)
        }
      case For(init, cond, update, body) =>
        val exit = new Label
        emitStmt(init)
        loop(emitExpr(cond), exit) {
          emitStmt(body)(mv, exit :: loopExits, ctx); emitStmt(update)
        }
      case Break()      => mv.visitJumpInsn(Opcodes.GOTO, loopExits.head)
      case Return(None) => mv.visitInsn(Opcodes.RETURN)
      case Return(Some(expr)) =>
        emitExpr(expr)
        mv.visitInsn(returnOp(expr.typ))
      case Print(exprs) =>
        exprs.foreach { expr =>
          printing(emitExpr(expr), expr.typ)
        }
    }
  }

  /**
    * Emit bytecode for an expression.
    * Code will be appended to the method writer.
    * The result (if exists) will be pushed into the operand stack.
    *
    * @param expr the expression
    * @param mv   the current method writer
    * @param ctx  the current context
    */
  def emitExpr(expr: Expr)(implicit mv: MethodVisitor, ctx: Context): Unit = {
    // printf(s"At ${expr.pos}, emitExpr(expr = $expr)\n")

    expr match {
      case IntLit(v)      => mv.visitLdcInsn(v)
      case BoolLit(v)     => mv.visitLdcInsn(v)
      case StringLit(str) => mv.visitLdcInsn(StringUtils.unquote(str))
      case NullLit()      => mv.visitInsn(Opcodes.ACONST_NULL)

      // Prebuilt functions
      case ReadInt()  => callScanner("nextInt")
      case ReadLine() => callScanner("nextLine")

      // Unary expressions
      case Unary(op, expr) =>
        emitExpr(expr)
        op match {
          case TreeNode.NEG => mv.visitInsn(Opcodes.INEG)
          case TreeNode.NOT =>
            // NOTE: !b = b xor 1
            mv.visitInsn(Opcodes.ICONST_1)
            mv.visitInsn(Opcodes.IXOR)
        }

      // Binary expressions
      case Binary(op, lhs, rhs) =>
        emitExpr(lhs)
        emitExpr(rhs)
        op match {
          case op: ArithOp => mv.visitInsn(arithOp(op))
          // Warning: JVM doesn't support operations directly on booleans. Thus, we always use integer instuctions on
          // them, i.e. IAND and IOR. Remember that LAND and LOR are for _long_ integers, not _logical_ and/or!
          case TreeNode.AND  => mv.visitInsn(Opcodes.IAND)
          case TreeNode.OR   => mv.visitInsn(Opcodes.IOR)
          case op: EqOrCmpOp => compare(op, lhs.typ)
        }

      // Local variables: they must be already assigned to an index
      case LocalVar(v) => mv.visitVarInsn(loadOp(v.typ), ctx.index(v))

      // Array related
      case NewArray(elemType, len) =>
        emitExpr(len)
        elemType.typ match {
          case t: JNativeType =>
            mv.visitIntInsn(Opcodes.NEWARRAY, arrayTypeCode(t))
          case t =>
            mv.visitTypeInsn(Opcodes.ANEWARRAY, toASMType(t).getInternalName)
        }
      case IndexSel(array, index) =>
        emitExpr(array)
        emitExpr(index)
        val elemType = array.typ.asInstanceOf[ArrayType].elemType
        mv.visitInsn(arrayLoadOp(elemType))
      case ArrayLen(array) =>
        emitExpr(array)
        mv.visitInsn(Opcodes.ARRAYLENGTH)

      // Class related
      case NewClass(clazz) =>
        mv.visitTypeInsn(Opcodes.NEW, internalName(clazz))
        mv.visitInsn(Opcodes.DUP)
        mv.visitMethodInsn(
          Opcodes.INVOKESPECIAL,
          internalName(clazz),
          CONSTRUCTOR_NAME,
          CONSTRUCTOR_DESC,
          false
        )

      case This() => mv.visitVarInsn(Opcodes.ALOAD, 0)

      case MemberVar(receiver, v) =>
        emitExpr(receiver)
        mv.visitFieldInsn(
          Opcodes.GETFIELD,
          internalName(v.owner),
          v.name,
          descriptor(v.typ)
        )

      case MemberMethod(receiver, method) =>
        // printf(s"receiver.typ = ${receiver.typ}\n")

        // 先处理好 receiver
        emitExpr(receiver)

        // 辅助函数类型
        val assistClassType =
          ClassType(
            method.owner.name + "$" + method.name,
            Some(ClassType(fromFunTypeToFunBaseClassName(method.typ), None))
          )

        // 保存现在在栈顶的receiver
        // 由于是临时使用，next 无需 +1
        val rcvIndex = ctx.next
        mv.visitVarInsn(storeOp(receiver.typ), rcvIndex)
        // new 一个函数对象
        mv.visitTypeInsn(
          Opcodes.NEW,
          internalName(assistClassType)
        )
        // 调用构造函数，构造函数会消耗一个栈顶的函数对象，所以这里 duplicate 一下
        mv.visitInsn(Opcodes.DUP)
        mv.visitMethodInsn(
          Opcodes.INVOKESPECIAL,
          internalName(assistClassType),
          CONSTRUCTOR_NAME,
          CONSTRUCTOR_DESC
        )
        // 为 self 赋值也会消耗函数对象，故这里再 duplicate 一发
        mv.visitInsn(Opcodes.DUP)
        // 把 receiver 丢回栈顶
        mv.visitVarInsn(loadOp(receiver.typ), rcvIndex)
        // 把新建的函数对象的self赋为receiver得到的对象
        mv.visitFieldInsn(
          Opcodes.PUTFIELD,
          internalName(assistClassType),
          "self",
          descriptor(receiver.typ)
        )

      case StaticMethod(owner, method) =>
        val assistClassType =
          ClassType(
            owner.name + "$" + method.name,
            Some(ClassType(fromFunTypeToFunBaseClassName(method.typ), None))
          )
        // new 一个函数对象
        mv.visitTypeInsn(
          Opcodes.NEW,
          internalName(assistClassType)
        )
        // 调用构造函数，构造函数会消耗一个栈顶的函数对象，所以这里 duplicate 一下
        mv.visitInsn(Opcodes.DUP)
        mv.visitMethodInsn(
          Opcodes.INVOKESPECIAL,
          internalName(assistClassType),
          CONSTRUCTOR_NAME,
          CONSTRUCTOR_DESC
        )

      case StaticCall(m, args) =>
        args foreach emitExpr
        mv.visitMethodInsn(
          Opcodes.INVOKESTATIC,
          internalName(m.owner),
          m.name,
          method_descriptor(m.typ),
          false
        )
      case MemberCall(receiver, m, args) =>
        (receiver :: args) foreach emitExpr

        // printf(s"MemberCall(receiver = $receiver, m = $m, args = $args)\n")
        // printf(s"descriptor(m) = ${method_descriptor(m.typ)}\n")

        mv.visitMethodInsn(
          Opcodes.INVOKEVIRTUAL,
          internalName(m.owner),
          m.name,
          method_descriptor(m.typ),
          false
        )

      case FunctionCall(fun, args) =>
        // 向操作栈中压入一个函数对象
        emitExpr(fun)
        // 向操作栈中压入若干个参数
        args foreach emitExpr
        // Q: 我知道这里有一个函数对象，但是如果我要调用它，我还需要知道这个函数对象所属的类的 internal name
        mv.visitMethodInsn(
          Opcodes.INVOKEVIRTUAL,
          internalName(
            fromFunTypeToFunBaseClassType(fun.typ.asInstanceOf[FunType])
          ),
          "apply",
          method_descriptor(fun.typ)
        )

      case el @ ExpressionLambda(params, expr, scope) =>
        // 加入所需基类
        functionTypes += el.typ.asInstanceOf[FunType]
        // 声明 lambda
        // 方便起见，声明时我们将所有的 lambda 表达式都统一视为 BlockLambda
        val lambdaIndex = lambdaTot
        lambdaTot += 1
        emitLambda(
          new BlockLambda(
            params,
            new Block(List(new Return(Some(expr))))(
              scope.nestedScope.asInstanceOf[LocalScope]
            ),
            scope
          )(el.typ),
          lambdaIndex,
          ctx.currentClassType,
          ctx.isStatic
        )
        // 方便起见，这里先预准备一些相关的类型
        val lambdaClassName = "Lambda$" + lambdaIndex
        val parentType = fromFunTypeToFunBaseClassType(
          el.typ.asInstanceOf[FunType]
        )
        val lambdaClassType = ClassType(lambdaClassName, Some(parentType))
        // new 一个函数对象
        mv.visitTypeInsn(
          Opcodes.NEW,
          internalName(lambdaClassType)
        )
        // 调用构造函数，构造函数会消耗一个栈顶的函数对象，所以这里 duplicate 一下
        mv.visitInsn(Opcodes.DUP)
        mv.visitMethodInsn(
          Opcodes.INVOKESPECIAL,
          internalName(lambdaClassType),
          CONSTRUCTOR_NAME,
          CONSTRUCTOR_DESC
        )
        if (!ctx.isStatic) {
          // 为 self 赋值会消耗函数对象，故这里再 duplicate 一发
          mv.visitInsn(Opcodes.DUP)
          // this 应该存于 index = 0 的临时变量中，将其 load 到栈顶
          mv.visitVarInsn(loadOp(ctx.currentClassType), 0)
          // 把新建的函数对象的self赋为receiver得到的对象
          mv.visitFieldInsn(
            Opcodes.PUTFIELD,
            internalName(lambdaClassType),
            "_self",
            descriptor(ctx.currentClassType)
          )
        }
        scope.captured.map(
          p => { // p 是一个 [[LocalVarSymbol]]
            // 赋值总会消耗函数对象，故这里再 duplicate 一发
            mv.visitInsn(Opcodes.DUP)
            // 将所需的临时变量 load 到栈顶
            mv.visitVarInsn(loadOp(p.typ), ctx.index(p))
            // 把新建的函数对象的self赋为receiver得到的对象
            mv.visitFieldInsn(
              Opcodes.PUTFIELD,
              internalName(lambdaClassType),
              p.name,
              descriptor(p.typ)
            )
          }
        )

      case bl @ BlockLambda(params, block, scope) =>
        // 加入所需基类
        functionTypes += bl.typ.asInstanceOf[FunType]
        // 声明 lambda
        // 方便起见，声明时我们将所有的 lambda 表达式都统一视为 BlockLambda
        val lambdaIndex = lambdaTot
        lambdaTot += 1
        emitLambda(bl, lambdaIndex, ctx.currentClassType, ctx.isStatic)
        // 方便起见，这里先预准备一些相关的类型
        val lambdaClassName = "Lambda$" + lambdaIndex
        val parentType = fromFunTypeToFunBaseClassType(
          bl.typ.asInstanceOf[FunType]
        )
        val lambdaClassType = ClassType(lambdaClassName, Some(parentType))
        // new 一个函数对象
        mv.visitTypeInsn(
          Opcodes.NEW,
          internalName(lambdaClassType)
        )
        // 调用构造函数，构造函数会消耗一个栈顶的函数对象，所以这里 duplicate 一下
        mv.visitInsn(Opcodes.DUP)
        mv.visitMethodInsn(
          Opcodes.INVOKESPECIAL,
          internalName(lambdaClassType),
          CONSTRUCTOR_NAME,
          CONSTRUCTOR_DESC
        )
        if (!ctx.isStatic) {
          // 为 self 赋值会消耗函数对象，故这里再 duplicate 一发
          mv.visitInsn(Opcodes.DUP)
          // this 应该存于 index = 0 的临时变量中，将其 load 到栈顶
          mv.visitVarInsn(loadOp(ctx.currentClassType), 0)
          // 把新建的函数对象的self赋为receiver得到的对象
          mv.visitFieldInsn(
            Opcodes.PUTFIELD,
            internalName(lambdaClassType),
            "_self",
            descriptor(ctx.currentClassType)
          )
        }
        scope.captured.map(
          p => { // p 是一个 [[LocalVarSymbol]]
            // 赋值总会消耗函数对象，故这里再 duplicate 一发
            mv.visitInsn(Opcodes.DUP)
            // 将所需的临时变量 load 到栈顶
            mv.visitVarInsn(loadOp(p.typ), ctx.index(p))
            // 把新建的函数对象的self赋为receiver得到的对象
            mv.visitFieldInsn(
              Opcodes.PUTFIELD,
              internalName(lambdaClassType),
              p.name,
              descriptor(p.typ)
            )
          }
        )

      case ClassTest(obj, clazz) =>
        emitExpr(obj)
        mv.visitTypeInsn(Opcodes.INSTANCEOF, internalName(clazz))
      case ClassCast(obj, clazz) =>
        emitExpr(obj)
        mv.visitTypeInsn(Opcodes.CHECKCAST, internalName(clazz))
    }
  }

  var functionTypes: mutable.Set[FunType] = mutable.Set.empty[FunType]
  var assistMethods: mutable.ArrayBuffer[(ClassDef, MethodDef)] =
    mutable.ArrayBuffer.empty[(ClassDef, MethodDef)]
  var lambdaJVMClasses: mutable.ArrayBuffer[JVMClass] =
    mutable.ArrayBuffer.empty[JVMClass]

  var lambdaTot = 0
}
