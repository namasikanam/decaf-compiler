package decaf.frontend.typecheck

import decaf.driver.error._
import decaf.driver.{Config, Phase}
import decaf.frontend.annot.ScopeImplicit._
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.parsing.Pos
import decaf.frontend.tree.SyntaxTree.NoAnnot
import decaf.frontend.tree.TreeNode._
import decaf.frontend.tree.TypedTree._
// Even I remain "Syn" existing here,
// the syntax tree de facto won't be used in this file.
import decaf.frontend.tree.{SyntaxTree => Syn}
import decaf.lowlevel.log.IndentPrinter
import decaf.printing.PrettyScope
import java.beans.Expression

/**
  * The typer phase: type check every statement and expression. It starts right after [[Namer]].
  *
  * Typer will NOT be interrupted by any type error. Instead, an ill-typed term will either be filled with a guessed
  * type, if this term could only be of that type in some situations, or we replace it with an error node.
  *
  * @see [[Namer]]
  * @see [[decaf.frontend.annot.Type]]
  */
class Typer(implicit config: Config)
    extends Phase[Tree, Tree]("typer", config)
    with Util {

  /**
    * Transformer entry.
    *
    * @param tree a typed tree with untyped holes
    * @return a fully typed (i.e. without holes) tree if succeeds
    */
  override def transform(tree: Tree): Tree = {
    val global = new ScopeContext(tree.scope)
    val checkedClasses = tree.classes.map {
      case clazz @ ClassDef(id, parent, fields, modifiers) =>
        val symbol = clazz.symbol
        val ctx = global.open(symbol.scope)
        val checkedFields = fields.map {
          case v: VarDef => v
          case m @ MethodDef(mod, id, methodReturnTypeLit, params, body) =>
            val formalCtx = ctx.open(m.symbol.scope)

            // printf(s"Check method $m\n")

            val (checkedBody, blockReturnType) = checkBlock(body)(formalCtx)

            // printf(s"After check the block of the method, blockReturnType = $blockReturnType\n")

            // Check if the body always returns a value, when the method is non-void
            if (!m.isAbstract && !methodReturnTypeLit.typ.isVoidType && (!blockReturnType.noError || blockReturnType.isVoidType))
              issue(new MissingReturnError(checkedBody.pos))

            MethodDef(mod, id, methodReturnTypeLit, params, checkedBody)(m.symbol)
              .setPos(m.pos)
        }
        ClassDef(id, parent, checkedFields)(symbol).setPos(clazz.pos)
    }

    TopLevel(checkedClasses)(tree.scope).setPos(tree.pos)
  }

  /**
    * After type checking succeeds, pretty print scopes if necessary.
    *
    * @param tree the typed tree
    */
  override def onSucceed(tree: Tree): Unit = {
    if (config.target == Config.Target.PA2) {
      val printer = new PrettyScope(new IndentPrinter(config.output))
      printer.pretty(tree.scope)
      printer.flush()
    }
  }

  /**
    * Type check a statement block.
    *
    * @param block      statement block
    * @param ctx        scope context
    * @param insideLoop are we inside a loop? This exists for check stmt [[Break]].
    * @return a pair: the typed block, and a boolean indicating if this block returns a value
    */
  def checkBlock(block: Block)(
      implicit ctx: ScopeContext,
      insideLoop: Boolean = false
  ): (Block, Type) = {
    val localCtx = ctx.open(block.scope)

    // printf(s"At ${block.pos}, checkBlock, now localCtx.currentMethod = ${localCtx.currentMethod}\n")

    val ss = block.stmts.map { checkStmt(_)(localCtx, insideLoop) }
    // Find the last [[stmt]] who has a correct return type
    val returnTypes = ss.filter(
        _._2 != NoType
    ).map(_._2)
    val returnType = returnTypes.length match {
        case 0 => VoidType
        case 1 => returnTypes.head
        case _ => returnTypes.reduce(typeUpperBound2)
    }

    (Block(ss.map(_._1))(block.scope).setPos(block.pos), returnType)
  }

  /**
    * Type check a statement.
    *
    * @param stmt       statement
    * @param ctx        scope context
    * @param insideLoop are we inside a loop?
    * @return a pair: the typed statement, and a boolean indicating if this statement returns a value
    */
  def checkStmt(
      stmt: Stmt
  )(implicit ctx: ScopeContext, insideLoop: Boolean): (Stmt, Type) = {
    // printf(s"At ${stmt.pos}, checkStmt $stmt\n")

    val checked = stmt match {
      case block: Block => checkBlock(block)

      case v: LocalVarDef =>
        v.init match {
          case Some(expr) =>
            // Special: we need to be careful that the initializer may cyclically refer to the declared variable, e.g.
            // var x = x + 1.
            //     ^
            //     before pos
            // So, we must rectify the "before pos" as the position of the declared variable.
            correctBeforePos = Some(v.id.pos)
            initializedID = Some(v.id)
            val r = typeExpr(expr)
            correctBeforePos = None // recover
            initializedID = None

            val typeLit = v.typeLit match {
              case TVar() =>
                // printf(s"Auto inference: type = ${r.typ}\n")

                val t = fromTypeToTypeLit(r.typ)
                t match {
                  case TVoid() | TVar() =>
                    issue(new DeclVoidTypeError(v.id.name, v.pos))
                  case _ => ;
                }
                t
              case t => t
            }
            if (!(r.typ <= typeLit.typ)) {
              issue(
                new IncompatBinOpError("=", typeLit.typ, r.typ, v.assignPos)
              )
            } else
              ctx.declare(new LocalVarSymbol(v, typeLit.typ))
            (LocalVarDef(typeLit, v.id, Some(r))(v.symbol), NoType)
          case None =>
            v.typeLit match {
              case TVar() => issue(new DeclVoidTypeError(v.id.name, v.pos))
              case _      => ;
            }
            (v, NoType)
        }

      case Assign(lhs, rhs) =>
        val l = typeLValue(lhs)
        val r = typeExpr(rhs)
        l match {
            case m: MemberMethod => issue(new AssignMethodError(m.variable.name, stmt.pos))
            case m: StaticMethod => issue(new AssignMethodError(m.variable.name, stmt.pos))
            case v: LocalVar =>
                // if (ctx.currentScope.isLambda && v.variable.domain.isLocal && v.variable.domain != ctx.currentScope)

                // printf(s"Assign a local var:\n domain = ${v.variable.domain},\n scopes = ${ctx.scopes.mkString("\n")}\nEndAssign\n")

                if (ctx.currentScope.isLambda && v.variable.domain.isLocal && !checkSameLocal(v.variable.domain, ctx.scopes))
                    issue(new AssCapturedError(stmt.pos))
            case _ =>
        }
        l.typ match {
          case NoType => // do nothing
          case t if !(r.typ <= t) =>
            issue(new IncompatBinOpError("=", l.typ, r.typ, stmt.pos))
          case _ => // do nothing
        }
        (Assign(l, r), NoType)

      case ExprEval(expr) =>
        val e = typeExpr(expr)
        (ExprEval(e), NoType)

      case Skip() => (Skip(), NoType)

      case If(cond, trueBranch, falseBranch) =>
        val c = checkTestExpr(cond)
        val (t, trueReturnType) = checkBlock(trueBranch)
        val f = falseBranch.map(checkBlock)
        // if-stmt returns a value if both branches return
        val returns = typeUpperBound2(trueReturnType, f.getOrElse((NoType, NoType))._2)
        (If(c, t, f.map(_._1)), returns)

      case While(cond, body) =>
        val c = checkTestExpr(cond)
        val (b, _) = checkBlock(body)(ctx, insideLoop = true)
        (While(c, b), NoType)

      case For(init, cond, update, body) =>
        // Since `init` and `update` may declare local variables, remember to first open the local scope of `body`.
        val local = ctx.open(body.scope)
        val (i, _) = checkStmt(init)(local, insideLoop)
        val c = checkTestExpr(cond)(local)
        val (u, _) = checkStmt(update)(local, insideLoop)
        val ss = body.stmts.map { checkStmt(_)(local, insideLoop = true) }
        val b = Block(ss.map(_._1))(body.scope)
        (For(i, c, u, b), NoType)

      case Break() =>
        if (!insideLoop) issue(new BreakOutOfLoopError(stmt.pos))
        (Break(), NoType)

      case Return(expr) =>
        // printf(s"Return:\n ctx.currentMethod = ${ctx.currentMethod}\n")
        // printf(s"ctx.currentMethod.typ = ${ctx.currentMethod.typ}")
        // printf(s"ctx.currentMethod.typ.ret = ${ctx.currentMethod.typ.ret}")

        val expected = ctx.currentMethod.typ.ret
        val e = expr match {
          case Some(e1) => Some(typeExpr(e1))
          case None     => None
        }
        val actual = e.map(_.typ).getOrElse(VoidType)
        if (actual.noError && !ctx.currentScope.isLambda && !(actual <= expected))
          issue(new BadReturnTypeError(expected, actual, stmt.pos))
        (Return(e), e match {
            case Some(e1) => e1.typ
            case None => NoType
        })

      case Print(exprs) =>
        val es = exprs.zipWithIndex.map {
          case (expr, i) =>
            val e = typeExpr(expr)
            if (e.typ.noError && !e.typ.isBaseType)
              issue(new BadPrintArgError(i + 1, e.typ, expr.pos))
            e
        }
        (Print(es), NoType)
    }

    checked match {
      case (s, r) => (s.setPos(stmt.pos), r)
    }
  }

  /**
    * Check if an expression has type bool.
    *
    * @param expr expression
    * @param ctx  scope context
    * @return true if it has type bool
    */
  private def checkTestExpr(
      expr: Expr
  )(implicit ctx: ScopeContext): Expr = {
    val e = typeExpr(expr)
    if (e.typ !== BoolType) issue(new BadTestExpr(expr.pos))
    e
  }

  implicit val noType: NoType.type = NoType

  /**
    * Type check an expression.
    *
    * @param expr expression
    * @param ctx  scope context
    * @return typed expression
    */
  def typeExpr(expr: Expr)(implicit ctx: ScopeContext): Expr = {
    // printf(s"At testExpr(expr = $expr) at ${expr.pos}\n")

    val err = ErrorTypeExpr(expr)

    val typed = expr match {
      case e: LValue => typeLValue(e)

      case IntLit(v)    => IntLit(v)(IntType)
      case BoolLit(v)   => BoolLit(v)(BoolType)
      case StringLit(v) => StringLit(v)(StringType)
      case NullLit()    => NullLit()(NullType)

      case ReadInt()  => ReadInt()(IntType)
      case ReadLine() => ReadLine()(StringType)

      case Unary(op, operand) =>
        val e = typeExpr(operand)
        e.typ match {
          case NoType => // avoid nested errors
          case t =>
            if (!compatible(op, t))
              issue(new IncompatUnOpError(op, t, expr.pos))
        }
        // Even when it doesn't type check, we could make a fair guess based on the operator kind.
        // Let's say the operator is `-`, then one possibly wants an integer as the operand.
        // Once he/she fixes the operand, according to our type inference rule, the whole unary expression
        // must have type int! Thus, we simply _assume_ it has type int, rather than `NoType`.
        Unary(op, e)(resultTypeOf(op))

      case Binary(op, lhs, rhs) =>
        val l = typeExpr(lhs)
        val r = typeExpr(rhs)
        (l.typ, r.typ) match {
          case (_, NoType) | (NoType, _) => // avoid nested errors
          case (lt, rt) =>
            if (!compatible(op, lt, rt))
              issue(new IncompatBinOpError(op, lt, rt, expr.pos))
        }
        Binary(op, l, r)(resultTypeOf(op)) // make a fair guess

      case ExpressionLambda(params, retExpr, scope) =>
        val fctx = ctx.open(scope)
        val lctx = fctx.open(scope.nestedScope)
        val re = typeExpr(retExpr)(lctx)
        val typ = FunType(params.map(_.typeLit.typ), re.typ)
        scope.owner.asInstanceOf[LambdaSymbol].typ = typ
        ExpressionLambda(params, re, scope)(typ)

      case BlockLambda(params, block, scope) =>
        val fctx = ctx.open(scope)
        val lctx = fctx.open(scope.nestedScope)
        val (b, retTyp) = checkBlock(block)(lctx)
        val typ = FunType(params.map(_.typeLit.typ), retTyp)
        scope.owner.asInstanceOf[LambdaSymbol].typ = typ
        BlockLambda(params, b, scope)(typ)

      case UnTypedNewArray(elemType, length) =>
        val l = typeExpr(length)
        if (elemType.typ.isVoidType) issue(new BadArrElementError(elemType.pos))
        if (l.typ !== IntType) issue(new BadNewArrayLength(length.pos))
        NewArray(elemType, l)(ArrayType(elemType.typ)) // make a fair guess

      case UnTypedNewClass(id) =>
        ctx.global.find(id) match {
            case Some(clazz) =>
                if (clazz.isAbstract) {
                    issue(new NewAbstractError(id, expr.pos))
                    err
                } else NewClass(clazz)(clazz.typ)
            case None => issue(new ClassNotFoundError(id, expr.pos)); err
            }

      case This() =>
        if (ctx.currentMethod.isStatic)
            issue(new ThisInStaticFuncError(expr.pos))
        This()(ctx.currentClass.typ)

      // Call
      case call @ Call(VarSel(Some(VarSel(None, id)), method), _)
          if ctx.global.contains(id) =>
        // Special case: invoking a static method, like MyClass.foo()
        val clazz = ctx.global(id)
        clazz.scope.lookup(method) match {
          case Some(symbol) =>
            symbol match {
              case m: MethodSymbol =>
                if (m.isStatic) {
                  typeCall(call, None, m)
                } else {
                  issue(new NotClassFieldError(method, clazz.typ, method.pos));
                  err
                }
              case _ =>
                issue(new NotClassMethodError(method, clazz.typ, method.pos));
                err
            }
          case None =>
            // printf(
            //   "FieldNotFoundError in call1: expr = \"%s\"\n",
            //   expr.toString
            // )
            issue(new FieldNotFoundError(method, clazz.typ, method.pos)); err
        }

      case call @ Call(VarSel(receiver, method), args) =>
        // printf(s"Call((receiver = $receiver, method = $method), args = $args)\n")

        val r = receiver.map(typeExpr)
        r.map(_.typ) match {
          case Some(NoType) =>
            // printf("Here is no type!\n")

            err
          case Some(_: ArrayType)
              if method.name == "length" => // Special case: array.length()
            assert(r.isDefined)
            if (args.nonEmpty)
              issue(new BadLengthArgError(args.length, expr.pos))
            ArrayLen(r.get)(IntType)
          case Some(t @ ClassType(c, _)) =>
            ctx.global(c).scope.lookup(method) match {
              case Some(sym) =>
                sym match {
                  case m: MethodSymbol => typeCall(call, r, m)
                  case mv: MemberVarSymbol =>
                    issue(new CallUncallableError(mv.typ, expr.pos)); err
                  case _ =>
                    issue(new NotClassMethodError(method, t, method.pos)); err
                }
              case None =>
                if (receiver == None) {
                    issue(new UndeclVarError(method.name, method.pos)); err
                }
                else {
                    issue(new FieldNotFoundError(method.name, t, method.pos)); err
                }
            }
          case None =>
            ctx.lookupBefore(method, initializedID match {
                case Some(identifier) if identifier == method =>
                    correctBeforePos.getOrElse(method.pos)
                case _ => method.pos
            }) match {
                case Some(sym) => sym match {
                    case v: LocalVarSymbol =>
                        v.typ match {
                            case FunType(typArgs, ret) =>
                                if (typArgs.length != args.length) {
                                    issue(new BadArgCountError(v.name, typArgs.length, args.length, expr.pos))
                                }
                                val as = (typArgs zip args).zipWithIndex.map {
                                    case ((t, a), i) =>
                                    val e = typeExpr(a)
                                    if (e.typ.noError && !(e.typ <= t)) {
                                        issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                                    }
                                    e
                                }
                                FunctionCall(LocalVar(v)(v.typ), as)(ret)
                            case NoType => err
                            case _ =>
                                issue(new CallUncallableError(v.typ, expr.pos))
                                err
                        }
                    case m: MethodSymbol =>
                        // printf("Yes, None receiver, MethodSymbol~\n");

                        if (ctx.currentMethod.isStatic && !m.isStatic) {
                            issue(
                                new RefNonStaticError(
                                    m.name,
                                    ctx.currentMethod.name,
                                    call.expr.pos
                                )
                            )
                        }
                        m.typ match {
                            case FunType(typArgs, ret) =>
                            if (typArgs.length != args.length) {
                                issue(new BadArgCountError(m.name, typArgs.length, args.length, expr.pos))
                            }
                            val as = (typArgs zip args).zipWithIndex.map {
                                case ((t, a), i) =>
                                val e = typeExpr(a)
                                if (e.typ.noError && !(e.typ <= t)) {
                                    issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                                }
                                e
                            }
                            MemberCall(This(), m, as)(ret)
                        }
                    case _ =>
                        issue(new UndeclVarError(method, method.pos)); err
                }
                case None => issue(new UndeclVarError(method, method.pos)); err
            }
          case Some(t) =>
            issue(new NotClassFieldError(method, t, method.pos)); err
        }

      // TODO: I don't know how to call a simple function here……
      case call @ Call(func, args) =>
        val f = typeExpr(func)
        f.typ match {
          case NoType => err
          case FunType(typArgs, ret) =>
            if (typArgs.length != args.length) {
                issue(new LambdaBadArgCountError(typArgs.length, args.length, expr.pos))
            }
            val as = (typArgs zip args).zipWithIndex.map {
                case ((t, a), i) =>
                val e = typeExpr(a)
                if (e.typ.noError && !(e.typ <= t)) {
                    issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                }
                e
            }
            FunctionCall(f, as)(ret)
          case _ =>
            issue(new CallUncallableError(f.typ, expr.pos))
            err
        }

      case UnTypedClassTest(obj, clazz) =>
        val o = typeExpr(obj)
        if (!o.typ.isClassType) issue(new NotClassError(o.typ, o.pos))
        ctx.global.find(clazz) match {
            case Some(c) => ClassTest(o, c)(BoolType)
            case None    => issue(new ClassNotFoundError(clazz.name, expr.pos)); err
        }

      case UnTypedClassCast(obj, clazz) =>
        val o = typeExpr(obj)
        if (!o.typ.isClassType) issue(new NotClassError(o.typ, o.pos))
        ctx.global.find(clazz) match {
            case Some(c) => ClassCast(o, c)(c.typ)
            case None    => issue(new ClassNotFoundError(clazz.name, expr.pos)); err
        }
    }
    typed.setPos(expr.pos)
  }

  private def typeCall(
      call: Call,
      receiver: Option[Expr],
      method: MethodSymbol
  )(implicit ctx: ScopeContext): Expr = {
    // Cannot call this's member methods in a static method
    if (receiver.isEmpty && ctx.currentMethod.isStatic && !method.isStatic) {
      issue(
        new RefNonStaticError(
          method.name,
          ctx.currentMethod.name,
          call.expr.pos
        )
      )
    }
    val args = call.exprList
    if (method.arity != args.length) {
      issue(
        new BadArgCountError(method.name, method.arity, args.length, call.pos)
      )
    }
    val as = (method.typ.args zip args).zipWithIndex.map {
      case ((t, a), i) =>
        val e = typeExpr(a)
        if (e.typ.noError && !(e.typ <= t)) {
          issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
        }
        e
    }

    if (method.isStatic) {
      StaticCall(method, as)(method.returnType)
    } else {
      MemberCall(receiver.getOrElse(This()), method, as)(method.returnType)
    }
  }

  private def typeLValue(
      expr: LValue
  )(implicit ctx: ScopeContext): LValue = {
    val err = ErrorTypeLValue(expr)

    val typed = expr match {
      // Variable, which should be complicated since a legal variable could refer to a local var,
      // a visible member var (, and a class name).
      case VarSel(None, id) =>
        // printf("VarSel(None, " + id.name + ")\n")

        // Be careful we may be inside the initializer, if so, load the correct "before position".
        // TODO: [[if identifier != id]]
        ctx.lookupBefore(id, initializedID match {
            case Some(identifier) if identifier == id =>
                correctBeforePos.getOrElse(id.pos)
            case _ => id.pos
        }) match {
          case Some(sym) =>
            sym match {
              case v: LocalVarSymbol =>
                LocalVar(v)(v.typ)
              case v: MemberVarSymbol =>
                if (ctx.currentMethod.isStatic) // member vars cannot be accessed in a static method
                  {
                    issue(
                      new RefNonStaticError(
                        id,
                        ctx.currentMethod.name,
                        expr.pos
                      )
                    )
                  }
                MemberVar(This(), v)(v.typ)
              case m: MethodSymbol =>
                if (ctx.currentMethod.isStatic && !m.isStatic) // member vars cannot be accessed in a static method
                {
                    issue(
                        new RefNonStaticError(
                        id,
                        ctx.currentMethod.name,
                        expr.pos
                        )
                    )
                }
                MemberMethod(This(), m)(m.typ)
              case _ =>
                // printf("When typeChecking VarSel " + id.name + ", we find a strange symbol.\n")

                issue(new UndeclVarError(id, expr.pos)); err
            }
          case None =>
            // printf("VarSel fail to find " + id.name + ".\n")

            issue(new UndeclVarError(id, expr.pos)); err
        }

      case VarSel(Some(VarSel(None, id)), f)
          if ctx.global.contains(id) =>
        // special case like MyClass.foo: report error cannot access field 'foo' from 'class : MyClass'
        val clazz = ctx.global(id)
        clazz.scope.lookup(f) match {
          case Some(symbol) =>
            symbol match {
              case m: MethodSymbol =>
                if (m.isStatic) StaticMethod(clazz, m)(m.typ)
                else {
                  issue(new NotClassFieldError(f, clazz.typ, f.pos));
                  err
                }
              case _ => // Here's strange for me, but I have no choice.
                issue(new NotClassFieldError(f, clazz.typ, f.pos))
                // issue(new NotClassMethodError(f, clazz.typ, f.pos));
                err
            }
          case None =>
            issue(new FieldNotFoundError(f, clazz.typ, f.pos)); err
        }

      case VarSel(Some(receiver), id) =>
        val r = typeExpr(receiver)
        r.typ match {
          case NoType => err
          case t @ ClassType(c, _) =>
            ctx.global(c).scope.lookup(id) match {
              case Some(sym) =>
                sym match {
                  case v: MemberVarSymbol =>
                    if (!(ctx.currentClass.typ <= t)) // member vars are protected
                      {
                        issue(new FieldNotAccessError(id, t, expr.pos))
                      }
                    MemberVar(r, v)(v.typ)
                  case m: MethodSymbol =>
                    if (m.isStatic) { // TODO: Some unkown issue should occur here
                    }
                    MemberMethod(r, m)(m.typ)
                  case _ => issue(new FieldNotFoundError(id, t, expr.pos)); err
                }
              case None => issue(new FieldNotFoundError(id, t, expr.pos)); err
            }
          case t => issue(new NotClassFieldError(id, t, expr.pos)); err
        }

      case IndexSel(array, index) =>
        val a = typeExpr(array)
        val i = typeExpr(index)
        val typ = a.typ match {
          case ArrayType(elemType) =>
            if (i.typ !== IntType) issue(new SubNotIntError(expr.pos))
            elemType // make a fair guess
          case t =>
            if (t.noError) issue(new NotArrayError(array.pos))
            NoType
        }
        IndexSel(a, i)(typ)
    }
    typed.setPos(expr.pos)
  }

  private var correctBeforePos: Option[Pos] = None
  private var initializedID: Option[String] = None

  private def compatible(op: Op, operand: Type): Boolean = op match {
    case NEG => operand === IntType // if e : int, then -e : int
    case NOT => operand === BoolType // if e : bool, then !e : bool
  }

  private def compatible(op: Op, lhs: Type, rhs: Type): Boolean = op match {
    case _: ArithOp =>
      (lhs === IntType) && (rhs === IntType) // if e1, e2 : int, then e1 + e2 : int
    case _: LogicOp =>
      (lhs === BoolType) && (rhs === BoolType) // if e1, e2 : bool, then e1 && e2 : bool
    case _: EqOp =>
      (lhs <= rhs) || (rhs <= lhs) // if e1 : T1, e2 : T2, T1 <: T2 or T2 <: T1, then e1 == e2 : bool
    case _: CmpOp =>
      (lhs === IntType) && (rhs === IntType) // if e1, e2 : int, then e1 > e2 : bool
  }

  private def resultTypeOf(op: Op): Type = op match {
    case NEG                             => IntType
    case NOT                             => BoolType
    case _: ArithOp                      => IntType
    case _: LogicOp | _: EqOp | _: CmpOp => BoolType
  }
}
