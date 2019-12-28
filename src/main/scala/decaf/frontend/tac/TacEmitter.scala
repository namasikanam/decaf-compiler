package decaf.frontend.tac

import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot.{
  BoolType,
  IntType,
  LocalVarSymbol,
  StringType,
  FunType,
  FormalScope
}
import decaf.frontend.tree.TreeNode
import decaf.frontend.tree.TypedTree._
import decaf.lowlevel.StringUtils
import decaf.lowlevel.instr.Temp
import decaf.lowlevel.label.Label
import decaf.lowlevel.tac.{FuncVisitor, Intrinsic, RuntimeError, TacInstr}
import decaf.util.Conversions._

import scala.collection.mutable
import scala.util.Random
import scala.annotation.meta.param

/**
  * Helper methods for TAC emission.
  */
trait TacEmitter {

  class Context {

    /**
      * Allocated temps for every local variable.
      */
    var vars = new mutable.TreeMap[LocalVarSymbol, Temp]
  }

  /**
    * Emit code for a statement.
    *
    * @param stmt      statement
    * @param ctx       context
    * @param loopExits a list of labels indicating loop exits (the first label is the exit of the current loop)
    * @param fv        function visitor
    */
  def emitStmt(
      stmt: Stmt
  )(implicit ctx: Context, loopExits: List[Label], fv: FuncVisitor): Unit = {
    // printf(s"At ${stmt.pos}, stmt = $stmt\n")
    // printf(s"ctx.vars = ${ctx.vars}\n")

    stmt match {
      case Block(stmts) => stmts.foreach(emitStmt)

      case v: LocalVarDef =>
        val t = fv.freshTemp
        ctx.vars(v.symbol) = t
        v.init.foreach { expr =>
          val et = emitExpr(expr)
          fv.visitAssign(t, et)
        }

      case Assign(IndexSel(array, index), rhs) =>
        val at = emitExpr(array)
        val it = emitExpr(index)
        val addr = emitArrayElementAddress(at, it)
        val t = emitExpr(rhs)
        fv.visitStoreTo(addr, t)

      case Assign(MemberVar(receiver, v), rhs) =>
        val rcv = emitExpr(receiver)
        val rs = emitExpr(rhs)
        fv.visitMemberWrite(rcv, v.owner.name, v.name, rs)

      case Assign(LocalVar(v), rhs) =>
        val t = emitExpr(rhs)
        fv.visitAssign(ctx.vars(v), t)

      case ExprEval(expr) => emitExpr(expr)
      case Skip()         => // nop

      case If(cond, trueBranch, falseBranch) =>
        val t = emitExpr(cond)
        falseBranch match {
          case Some(f) => ifThenElse(t, emitStmt(trueBranch), emitStmt(f))
          case None    => ifThen(t, emitStmt(trueBranch))
        }

      case While(cond, body) =>
        val exit = fv.freshLabel
        loop(emitExpr(cond), emitStmt(body)(ctx, exit :: loopExits, fv), exit)
      case For(init, cond, update, body) =>
        val exit = fv.freshLabel
        emitStmt(init)
        loop(emitExpr(cond), {
          emitStmt(body)(ctx, exit :: loopExits, fv)
          emitStmt(update)
        }, exit)
      case Break() => fv.visitBranch(loopExits.head)

      case Return(None) => fv.visitReturn()
      case Return(Some(expr)) =>
        val t = emitExpr(expr)
        fv.visitReturn(t)

      case Print(exprs) =>
        exprs.foreach {
          case e if e.typ === IntType =>
            val t = emitExpr(e)
            fv.visitIntrinsicCall(Intrinsic.PRINT_INT, t)
          case e if e.typ === BoolType =>
            val t = emitExpr(e)
            fv.visitIntrinsicCall(Intrinsic.PRINT_BOOL, t)
          case e if e.typ === StringType =>
            val t = emitExpr(e)
            fv.visitIntrinsicCall(Intrinsic.PRINT_STRING, t)
        }
    }
  }

  /**
    * Emit code for an expression.
    *
    * @param expr expression
    * @param ctx  context
    * @param fv   function visitor
    * @return a temp storing the value of this expression
    */
  def emitExpr(expr: Expr)(implicit ctx: Context, fv: FuncVisitor): Temp = {
    // printf(s"At ${expr.pos}, emitExpr(expr = $expr)\n")

    expr match {
      case IntLit(value)    => fv.visitLoad(value)
      case BoolLit(value)   => fv.visitLoad(value)
      case StringLit(value) => fv.visitLoad(StringUtils.unquote(value))
      case NullLit()        => fv.visitLoad(0)

      case ReadInt()  => fv.visitIntrinsicCall(Intrinsic.READ_INT, true)
      case ReadLine() => fv.visitIntrinsicCall(Intrinsic.READ_LINE, true)

      case LocalVar(v) => ctx.vars(v)

      case Unary(op, operand) =>
        val opcode = op match {
          case TreeNode.NEG => TacInstr.Unary.Op.NEG
          case TreeNode.NOT => TacInstr.Unary.Op.LNOT
        }
        val t = emitExpr(operand)
        fv.visitUnary(opcode, t)

      case Binary(op, lhs, rhs)
          if (op == TreeNode.EQ || op == TreeNode.NE) && lhs.typ === StringType =>
        // string eq/ne
        val lt = emitExpr(lhs)
        val rt = emitExpr(rhs)
        val result = fv.visitIntrinsicCall(Intrinsic.STRING_EQUAL, true, lt, rt)
        if (op == TreeNode.NE) {
          fv.visitUnarySelf(TacInstr.Unary.Op.LNOT, result)
        }
        result

      case Binary(op, lhs, rhs) =>
        import decaf.lowlevel.tac.TacInstr
        val opcode = op match {
          case TreeNode.ADD => TacInstr.Binary.Op.ADD
          case TreeNode.SUB => TacInstr.Binary.Op.SUB
          case TreeNode.MUL => TacInstr.Binary.Op.MUL
          case TreeNode.DIV => TacInstr.Binary.Op.DIV
          case TreeNode.MOD => TacInstr.Binary.Op.MOD
          case TreeNode.EQ  => TacInstr.Binary.Op.EQU
          case TreeNode.NE  => TacInstr.Binary.Op.NEQ
          case TreeNode.LT  => TacInstr.Binary.Op.LES
          case TreeNode.LE  => TacInstr.Binary.Op.LEQ
          case TreeNode.GT  => TacInstr.Binary.Op.GTR
          case TreeNode.GE  => TacInstr.Binary.Op.GEQ
          case TreeNode.AND => TacInstr.Binary.Op.LAND
          case TreeNode.OR  => TacInstr.Binary.Op.LOR
        }

        val lt = emitExpr(lhs)
        val rt = emitExpr(rhs)

        // Check: The dividing number can't be zero
        if (opcode == TacInstr.Binary.Op.DIV || opcode == TacInstr.Binary.Op.MOD) {
          val zero = fv.visitLoad(0)
          ifThen(fv.visitBinary(TacInstr.Binary.Op.EQU, rt, zero), {
            fv.visitPrint(RuntimeError.DIVISION_BY_ZERO)
            fv.visitIntrinsicCall(Intrinsic.HALT)
          })
        }

        fv.visitBinary(opcode, lt, rt)

      case NewArray(_, length) =>
        val lt = emitExpr(length)
        val eai = emitArrayInit(lt)

        // printf(s"emitArrayInit(_) = $eai\n")

        eai
      case IndexSel(array, index) =>
        val at = emitExpr(array)
        val it = emitExpr(index)
        val addr = emitArrayElementAddress(at, it)
        fv.visitLoadFrom(addr)
      case ArrayLen(array) =>
        val at = emitExpr(array)
        fv.visitLoadFrom(at, -4)

      case NewClass(clazz) => fv.visitNewClass(clazz.name)

      case This() =>
        if (currentFormalScope.isDefined) {
          val _T0 = fv.getArgTemp(0)
          fv.visitLoadFrom(_T0, 4)
        } else {
          fv.getArgTemp(0)
        }

      case MemberVar(receiver, variable) =>
        val rt = emitExpr(receiver)
        fv.visitMemberAccess(rt, variable.owner.name, variable.name)

      case MemberMethod(receiver, method) =>
        // 访问 expr.receiver
        val rcvr = emitExpr(receiver)

        // printf(s"At ${expr.pos}, MemberMethod($receiver, $method)\n")

        // newMv = mv.freshFunc(随便起个名字，函数类型的参数数量 + 1);
        val methodName = "member:(" + rcvr.toString + ")." + method.name + "@" + Random.alphanumeric
          .take(10)
          .mkString
        val newFv = fv.freshFunc(methodName, method.typ.args.length + 1)

        // 在 newMv 中生成 this_ = *(_T0 + 4)
        // _T0 是函数对象，偏移量4处存储的是一个对象指针
        val this_ = newFv.visitLoadFrom(newFv.getArgTemp(0), 4)

        // args = ArrayList{_T1, ..., _T{函数类型的参数数量}}
        val args = List
          .range(1, method.typ.args.length + 1)
          .map(i => newFv.getArgTemp(i))

        if (method.typ.ret.isVoidType) {
          newFv.visitMemberCall(this_, method.owner.name, method.name, args)
        } else {
          // ret = newMv.visitMemberCall(this_, 类名字, 函数名字, args, true) // 这调用的是普通函数，所以可以参考原来的调用普通函数的代码
          val ret = newFv.visitMemberCall(
            this_,
            method.owner.name,
            method.name,
            args,
            true
          )
          // 在 newMv 中生成 return ret
          newFv.visitReturn(ret)
        }

        // newMv.visitEnd()
        newFv.visitEnd()

        // 在 mv 中生成 result = ALLOCATE(8)
        val eight = fv.visitLoad(8)
        val result = fv.visitIntrinsicCall(Intrinsic.ALLOCATE, true, eight)

        // 在 mv 中生成 func = 从新虚表中获取新生成的函数，这需要一个偏移量，你应该在前几步中把它维护好
        // 依据文档，这里需要存一个函数指针
        val func = fv.visitFunction(methodName)

        // 在 mv 中生成 *(result + 0) = func
        fv.visitStoreTo(result, 0, func)

        // 在 mv 中生成 *(result + 4) = expr.receiver
        fv.visitStoreTo(result, 4, rcvr)

        // expr.val = result
        result

      case StaticMethod(owner, method) =>
        // newFv = fv.freshFunc(随便起个名字，函数类型的参数数量)
        val methodName = "static:" + owner.name + "." + method.name + "@" + Random.alphanumeric
          .take(10)
          .mkString

        // 雖然 _T0 傳進來的參數沒有什麼用處，但為了調用的一致性這裡仍需要為它留一個位置
        val newFv = fv.freshFunc(
          methodName,
          method.typ.args.size() + 1
        )

        // args = ArrayList{_T1, ..., _T{函数类型的参数数量}}
        val args = List
          .range(1, method.typ.args.length + 1)
          .map((i: Int) => newFv.getArgTemp(i))

        if (method.typ.ret.isVoidType) {
          // ret = newFv.visitStaticCall(, args, true) // 这调⽤的是普通函数，所以可以参考原来的调⽤普通函数的代码
          newFv.visitStaticCall(owner.name, method.name, args)
        } else {
          // ret = newFv.visitStaticCall(, args, true) // 这调⽤的是普通函数，所以可以参考原来的调⽤普通函数的代码
          val ret = newFv.visitStaticCall(owner.name, method.name, args, true)
          // 在 newFv 中⽣成 return ret
          newFv.visitReturn(ret)
        }

        // newFv.visitEnd()
        newFv.visitEnd()

        // 在 fv 中⽣成 result = ALLOCATE(4)
        val four = fv.visitLoad(4)
        val result = fv.visitIntrinsicCall(Intrinsic.ALLOCATE, true, four);

        // 在mv中⽣成 func = 从新虚表中获取新生成的函数，这需要一个偏移量，你应该在前几步中把它维护好
        val func = fv.visitFunction(methodName)

        // 在mv中⽣成 *(result + 0) = func
        fv.visitStoreTo(result, 0, func)

        // expr.val = result
        result

      case ExpressionLambda(params, expr, scope) =>
        // printf(s"captured = ${scope.captured}\n")

        // 記錄當前是在這個Lambda中 // 此時不再需要棧了
        val pastFormalScope = currentFormalScope
        currentFormalScope = Some(scope)

        // newFv = fv.freshFunc(隨便起個名字，函數類型的參數數量 + 1)
        val lambdaName = "lambda:(" + params + ")=>" + expr + "@" + Random.alphanumeric
          .take(10)
          .mkString

        val newFv = fv.freshFunc(
          lambdaName,
          params.size() + 1
        )

        var ctxLambda = new Context
        ctxLambda.vars = ctx.vars.clone()
        var i = 0
        for (i <- 0 to params.size() - 1) {
          ctxLambda.vars.update(params(i).symbol, newFv.getArgTemp(i + 1))
        }
        for (i <- 0 to scope.captured.size() - 1) {
          ctxLambda.vars.update(
            scope.captured(i),
            newFv.visitLoadFrom(newFv.getArgTemp(0), 8 + i * 4)
          )
        }

        // 在 newFv 中生成 expr 的 TAC 代碼
        val e = emitExpr(expr)(ctxLambda, newFv)
        newFv.visitReturn(e)

        // newFv.visitEnd()
        newFv.visitEnd()

        // 在 fv 中生成 result = ALLOCATE(4 * 被捕獲的變量數 + 8)
        val result_length = fv.visitLoad(4 * scope.captured.size() + 8)
        val result =
          fv.visitIntrinsicCall(Intrinsic.ALLOCATE, true, result_length)

        // 在 fv 中生成 func = 從新虛表中獲取新生成的函數，這需要一個偏移量，你應該在前幾步中把它維護好
        val func = fv.visitFunction(lambdaName)

        // 在 fv 中生成 *(result + 0) = func
        fv.visitStoreTo(result, 0, func)

        // 在 fv 中生成 *(result + 4) = this
        // If the function object is passed as the first argument
        if (fv.argsTemps.length > 0) {
          if (pastFormalScope.isDefined) {
            val _T0 = fv.getArgTemp(0)
            val this_ = fv.visitLoadFrom(_T0, 4)
            fv.visitStoreTo(result, 4, this_)
          } else {
            // For static function, this is wrong, but doesn't have influence.
            val this_ = fv.getArgTemp(0)
            fv.visitStoreTo(result, 4, this_)
          }
        }

        // for i in 0..被捕獲的變量數
        //    在 fv 中生成 *(result + (i * 4 + 8)) = 第 i 個被捕獲的變量
        for (i <- 0 to scope.captured.size() - 1) {
          fv.visitStoreTo(result, i * 4 + 8, ctx.vars(scope.captured(i)))
        }

        // 記錄當前是在原來的lambda中
        currentFormalScope = pastFormalScope

        // expr.val = result
        result

      case BlockLambda(params, block, scope) =>
        // 記錄當前是在這個Lambda中 // 此時不再需要棧了

        val pastFormalScope = currentFormalScope
        currentFormalScope = Some(scope)

        // newFv = fv.freshFunc(隨便起個名字，函數類型的參數數量 + 1)
        val lambdaName = "lambda:(" + params + ")=>" + expr + "@" + Random.alphanumeric
          .take(10)
          .mkString

        val newFv = fv.freshFunc(
          lambdaName,
          params.size() + 1
        )

        var ctxLambda = new Context
        ctxLambda.vars = ctx.vars.clone()
        var i = 0
        for (i <- 0 to params.size() - 1) {
          ctxLambda.vars.update(params(i).symbol, newFv.getArgTemp(i + 1))
        }
        for (i <- 0 to scope.captured.size() - 1) {
          ctxLambda.vars.update(
            scope.captured(i),
            newFv.visitLoadFrom(newFv.getArgTemp(0), 8 + i * 4)
          )
        }

        // 在 newFv 中生成 expr 的 TAC 代碼
        emitStmt(block)(ctxLambda, Nil, newFv)

        // newFv.visitEnd()
        newFv.visitEnd()

        // 在 fv 中生成 result = ALLOCATE(4 * 被捕獲的變量數 + 8)
        val result_length = fv.visitLoad(4 * scope.captured.size() + 8)
        val result =
          fv.visitIntrinsicCall(Intrinsic.ALLOCATE, true, result_length)

        // 在 fv 中生成 func = 從新虛表中獲取新生成的函數，這需要一個偏移量，你應該在前幾步中把它維護好
        val func = fv.visitFunction(lambdaName)

        // 在 fv 中生成 *(result + 0) = func
        fv.visitStoreTo(result, 0, func)

        // 在 fv 中生成 *(result + 4) = this
        // If the function object is passed as the first argument
        if (fv.argsTemps.length > 0) {
          if (pastFormalScope.isDefined) {
            val _T0 = fv.getArgTemp(0)
            val this_ = fv.visitLoadFrom(_T0, 4)
            fv.visitStoreTo(result, 4, this_)
          } else {
            // For static function, this is wrong, but doesn't have influence.
            val this_ = fv.getArgTemp(0)
            fv.visitStoreTo(result, 4, this_)
          }
        }

        // for i in 0..被捕獲的變量數
        //    在 fv 中生成 *(result + (i * 4 + 8)) = 第 i 個被捕獲的變量
        for (i <- 0 to scope.captured.size() - 1) {
        //   printf(
        //     s"captured(${scope.captured(i)}) = ${ctx.vars(scope.captured(i))}\n"
        //   );

          fv.visitStoreTo(result, i * 4 + 8, ctx.vars(scope.captured(i)))
        }

        // 記錄當前是在原來的 lambda 中
        currentFormalScope = pastFormalScope

        // expr.val = result
        result

      case MemberCall(receiver, method, args) =>
        val func = emitExpr(MemberMethod(receiver, method)(method.typ))
        val as = args.map(emitExpr)
        if (method.typ.ret.isVoidType) {
          fv.visitFunctionCall(func, as)
          null
        } else {
          fv.visitFunctionCall(func, as, true)
        }
      case StaticCall(method, args) =>
        val func = emitExpr(StaticMethod(method.owner, method)(method.typ))
        val as = args.map(emitExpr)
        if (method.typ.ret.isVoidType) {
          fv.visitFunctionCall(func, as)
          null
        } else {
          fv.visitFunctionCall(func, as, true)
        }

      case FunctionCall(function, args) =>
        // 访问 expr.func
        val func = emitExpr(function)

        // for arg in expr.args
        //    访问 arg
        val as = args.map(emitExpr)

        // 将 ret 保存到 expr.val 中
        if (function.typ.asInstanceOf[FunType].ret.isVoidType) {
          fv.visitFunctionCall(func, as)
          null
        } else {
          fv.visitFunctionCall(func, as, true)
        }

      //   case ArrayLenCall(array) =>
      // not required in PA3

      case ClassTest(obj, clazz) if obj.typ <= clazz.typ =>
        // Accelerate: when obj.type <: is.type, the test must be successful!
        fv.visitLoad(true)
      case ClassTest(obj, clazz) =>
        val ot = emitExpr(obj)
        emitClassTest(ot, clazz.name)
      case ClassCast(obj, clazz) if obj.typ <= clazz.typ =>
        // Accelerate: when obj.type <: is.type, the test must be successful!
        emitExpr(obj)
      case ClassCast(obj, clazz) =>
        val ot = emitExpr(obj)
        val result = emitClassTest(ot, clazz.name)
        /* Pseudo code:
         * {{{
         *     if (result != 0) branch exit  // cast success
         *     print "Decaf runtime error: " // RuntimeError.CLASS_CAST_ERROR1
         *     vtbl1 = *obj                  // vtable of obj
         *     fromClass = *(vtbl1 + 4)      // name of obj's class
         *     print fromClass
         *     print " cannot be cast to "   // RuntimeError.CLASS_CAST_ERROR2
         *     vtbl2 = load vtbl of the target class
         *     toClass = *(vtbl2 + 4)        // name of target class
         *     print toClass
         *     print "\n"                    // RuntimeError.CLASS_CAST_ERROR3
         *     halt
         * exit:
         * }}}
         */
        val exit = fv.freshLabel
        fv.visitBranch(TacInstr.CondBranch.Op.BNEZ, result, exit)
        fv.visitPrint(RuntimeError.CLASS_CAST_ERROR1)
        val vtbl1 = fv.visitLoadFrom(ot)
        val fromClass = fv.visitLoadFrom(vtbl1, 4)
        fv.visitIntrinsicCall(Intrinsic.PRINT_STRING, fromClass)
        fv.visitPrint(RuntimeError.CLASS_CAST_ERROR2)
        val vtbl2 = fv.visitLoadVTable(clazz.name)
        val toClass = fv.visitLoadFrom(vtbl2, 4)
        fv.visitIntrinsicCall(Intrinsic.PRINT_STRING, toClass)
        fv.visitPrint(RuntimeError.CLASS_CAST_ERROR3)
        fv.visitIntrinsicCall(Intrinsic.HALT)
        fv.visitLabel(exit)
        ot
    }
  }

  /**
    * Emit code for the following conditional statement:
    * {{{
    * if (cond) {
    * action
    * }
    * }}}
    * Implementation in pseudo code:
    * {{{
    * if (cond == 0) branch skip;
    * action
    * skip:
    * }}}
    *
    * @param cond   temp of condition
    * @param action code (to be generated) of the true branch
    * @param fv     function visitor
    */
  private def ifThen(cond: Temp, action: => Unit)(
      implicit fv: FuncVisitor
  ): Unit = {
    val skip = fv.freshLabel
    fv.visitBranch(TacInstr.CondBranch.Op.BEQZ, cond, skip)
    action
    fv.visitLabel(skip)
  }

  /**
    * Emit code for the following conditional statement:
    * {{{
    * if (cond) {
    * trueBranch
    * } else {
    * falseBranch
    * }
    * }}}
    * Implementation in pseudo code:
    * <pre>
    * if (cond == 0) branch skip
    * trueBranch
    * branch exit
    * skip:
    * falseBranch
    * exit:
    * </pre>
    *
    * @param cond        temp of condition
    * @param trueBranch  code (to be generated) of the true branch
    * @param falseBranch code (to be generated) of the false branch
    * @param fv          function visitor
    */
  private def ifThenElse(cond: Temp, trueBranch: => Unit, falseBranch: => Unit)(
      implicit fv: FuncVisitor
  ): Unit = {
    val skip = fv.freshLabel
    val exit = fv.freshLabel
    fv.visitBranch(TacInstr.CondBranch.Op.BEQZ, cond, skip)
    trueBranch
    fv.visitBranch(exit)
    fv.visitLabel(skip)
    falseBranch
    fv.visitLabel(exit)
  }

  /**
    * Emit code for the following loop:
    * <pre>
    * while (cond) {
    * block
    * }
    * </pre>
    * <p>
    * Implementation in pseudo code:
    * <pre>
    * entry:
    * cond = do test
    * if (cond == 0) branch exit
    * do block
    * branch entry
    * exit:
    * </pre>
    *
    * @param test  code (to be generated) of the loop condition
    * @param block code (to be generated) of the loop body
    * @param exit  label of loop exit
    * @param fv    function visitor
    */
  private def loop(test: => Temp, block: => Unit, exit: Label)(
      implicit fv: FuncVisitor
  ): Unit = {
    val entry = fv.freshLabel
    fv.visitLabel(entry)
    val cond = test
    fv.visitBranch(TacInstr.CondBranch.Op.BEQZ, cond, exit)
    block
    fv.visitBranch(entry)
    fv.visitLabel(exit)
  }

  /**
    * Emit code for initializing a new array.
    *
    * In memory, an array of length `n` takes `(n + 1) * 4` bytes, where
    *
    *     - the first 4 bytes: length
    *     - the rest bytes: data
    *
    * Pseudo code:
    * {{{
    * error = length < 0
    * if (error) {
    * throw RuntimeError.NEGATIVE_ARR_SIZE
    * }
    *
    * units = length + 1
    * size = units * 4
    * a = ALLOCATE(size)
    * *(a + 0) = length
    * p = a + size
    * p -= 4
    * while (p != a) {
    * *(p + 0) = 0
    * p -= 4
    * }
    * ret = (a + 4)
    * }}}
    *
    * @param length temp of array length
    * @param fv     function visitor
    * @return a temp storing the address of the first element of the array
    */
  private def emitArrayInit(length: Temp)(implicit fv: FuncVisitor): Temp = {
    val zero = fv.visitLoad(0)
    ifThen(fv.visitBinary(TacInstr.Binary.Op.LES, length, zero), {
      fv.visitPrint(RuntimeError.NEGATIVE_ARR_SIZE)
      fv.visitIntrinsicCall(Intrinsic.HALT)
    })
    val units = fv.visitBinary(TacInstr.Binary.Op.ADD, length, fv.visitLoad(1))
    val four = fv.visitLoad(4)
    val size = fv.visitBinary(TacInstr.Binary.Op.MUL, units, four)
    val a = fv.visitIntrinsicCall(Intrinsic.ALLOCATE, true, size)
    fv.visitStoreTo(a, length)
    val p = fv.visitBinary(TacInstr.Binary.Op.ADD, a, size)
    fv.visitBinarySelf(TacInstr.Binary.Op.SUB, p, four)
    loop(fv.visitBinary(TacInstr.Binary.Op.NEQ, p, a), {
      fv.visitStoreTo(p, zero)
      fv.visitBinarySelf(TacInstr.Binary.Op.SUB, p, four)
    }, fv.freshLabel)
    fv.visitBinary(TacInstr.Binary.Op.ADD, a, four)
  }

  /**
    * Emit code for computing the address of an array element.
    *
    * Pseudo code:
    * {{{
    * length = *(array - 4)
    * error1 = index < 0
    * error2 = index >= length
    * error = error1 || error2
    * if (error) {
    * throw RuntimeError.ARRAY_INDEX_OUT_OF_BOUND
    * }
    *
    * offset = index * 4
    * ret = array + offset
    * }}}
    *
    * @param array temp of the array
    * @param index temp of the index
    * @param fv    function visitor
    * @return a temp storing the address of the element
    */
  private def emitArrayElementAddress(array: Temp, index: Temp)(
      implicit fv: FuncVisitor
  ): Temp = {
    val length = fv.visitLoadFrom(array, -4)
    val zero = fv.visitLoad(0)
    val error1 = fv.visitBinary(TacInstr.Binary.Op.LES, index, zero)
    val error2 = fv.visitBinary(TacInstr.Binary.Op.GEQ, index, length)
    ifThen(fv.visitBinary(TacInstr.Binary.Op.LOR, error1, error2), {
      fv.visitPrint(RuntimeError.ARRAY_INDEX_OUT_OF_BOUND)
      fv.visitIntrinsicCall(Intrinsic.HALT)
    })
    val four = fv.visitLoad(4)
    val offset = fv.visitBinary(TacInstr.Binary.Op.MUL, index, four)
    fv.visitBinary(TacInstr.Binary.Op.ADD, array, offset)
  }

  /**
    * Emit code for testing if an object is an instance of class.
    *
    * Pseudo code:
    * {{{
    * target = LoadVtbl(clazz)
    * t = *object
    * loop:
    * ret = t == target
    * if (ret != 0) goto exit
    * t = *t
    * if (t != 0) goto loop
    * ret = 0 // t == null
    * exit:
    * }}}
    *
    * @param obj   temp of the object/instance
    * @param clazz name of the class
    * @param fv    function visitor
    * @return a temp storing the result (1 for true, and 0 for false)
    */
  private def emitClassTest(obj: Temp, clazz: String)(
      implicit fv: FuncVisitor
  ): Temp = {
    val target = fv.visitLoadVTable(clazz)
    val t = fv.visitLoadFrom(obj)
    val loop = fv.freshLabel
    val exit = fv.freshLabel
    fv.visitLabel(loop)
    val ret = fv.visitBinary(TacInstr.Binary.Op.EQU, t, target)
    fv.visitBranch(TacInstr.CondBranch.Op.BNEZ, ret, exit)
    fv.visitRaw(new TacInstr.Memory(TacInstr.Memory.Op.LOAD, t, t, 0))
    fv.visitBranch(TacInstr.CondBranch.Op.BNEZ, t, loop)
    val zero = fv.visitLoad(0)
    fv.visitAssign(ret, zero)
    fv.visitLabel(exit)
    ret
  }

  var currentFormalScope: Option[FormalScope] = None
}
