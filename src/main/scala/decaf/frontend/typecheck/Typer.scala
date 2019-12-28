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
import scala.collection.mutable

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

            val (checkedBody, blockReturnType, blockReturns) =
              checkBlock(body)(formalCtx)

            // printf(s"After check the block of the method, blockReturnType = $blockReturnType\n")

            // Only non-abstract method needs error checking
            if (!m.isAbstract) {
              // Check if the body always returns a value, when the method is non-void
              if (!methodReturnTypeLit.typ.isVoidType && !blockReturns)
                issue(new MissingReturnError(body.pos))
              if (blockReturnType == NoType)
                issue(new TypeIncompError(body.pos))
            }

            MethodDef(mod, id, methodReturnTypeLit, params, checkedBody)(
              m.symbol
            ).setPos(m.pos)
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
    * @return a 3-tuple: the typed block, return type, and a boolean indicating if this block returns a value
    */
  def checkBlock(block: Block)(
      implicit ctx: ScopeContext,
      insideLoop: Boolean = false
  ): (Block, Type, Boolean) = {
    val localCtx = ctx.open(block.scope)

    // printf(s"At ${block.pos}, checkBlock, now localCtx.currentMethod = ${localCtx.currentMethod}\n")

    val ss = block.stmts.map { checkStmt(_)(localCtx, insideLoop) }
    // Find the last [[stmt]] who has a correct return type
    val returnTypes = ss.filter(_._2 != EmptyType).map(_._2)
    val returnType = returnTypes.length match {
      case 0 => EmptyType
      case 1 => returnTypes.head
      case _ => returnTypes.reduce(typeUpperBound2)
    }

    (
      Block(ss.map(_._1))(block.scope).setPos(block.pos),
      returnType,
      !ss.filter(_._3).isEmpty
    )
  }

  /**
    * Type check a statement.
    *
    * @param stmt       statement
    * @param ctx        scope context
    * @param insideLoop are we inside a loop?
    * @return a 3-tuple: the typed statement, the type returned and a boolean indicating if this statement returns a value
    */
  def checkStmt(
      stmt: Stmt
  )(implicit ctx: ScopeContext, insideLoop: Boolean): (Stmt, Type, Boolean) = {
    // printf(s"At ${stmt.pos}, checkStmt $stmt\n")

    val checked = stmt match {
      case block: Block => checkBlock(block)

      case v: LocalVarDef =>
        v.init match {
          case Some(initExpr) =>
            // Special: we need to be careful that the initializer may cyclically refer to the declared variable, e.g.
            // var x = x + 1.
            //     ^
            //     before pos
            // So, we must rectify the "before pos" as the position of the declared variable.
            initVars += v.name
            val typeInitExpr = typeExpr(initExpr)
            initVars -= v.name

            var declTypeLit = v.typeLit match {
              case TVar() =>
                // printf(s"Auto inference: type = ${r.typ}\n")

                typeInitExpr.typ match {
                  case VoidType =>
                    issue(new DeclVoidTypeError(v.name, v.pos))
                    TError()
                  case t => fromTypeToTypeLit(t)
                }
              case t => t
            }
            if (!(typeInitExpr.typ <= declTypeLit.typ)) {
              issue(
                new IncompatBinOpError(
                  "=",
                  declTypeLit.typ,
                  typeInitExpr.typ,
                  v.assignPos
                )
              )
              declTypeLit = TError()
            }

            // printf(s"At ${stmt.pos}, LocalVarDef declTypeLit.typ = ${declTypeLit.typ}\n")

            val symbol = new LocalVarSymbol(v, declTypeLit.typ)
            ctx.declare(symbol)
            (
              LocalVarDef(declTypeLit, v.id, Some(typeInitExpr))(symbol),
              EmptyType,
              false
            )
          case None =>
            v.typeLit match {
              case TVar() =>
                issue(new DeclVoidTypeError(v.name, v.pos))

                val symbol = new LocalVarSymbol(v, NoType)
                ctx.declare(symbol)
                (LocalVarDef(TError(), v.id, None)(symbol), EmptyType, false)
              case _ => (v, EmptyType, false);
            }
        }

      case Assign(lhs, rhs) =>
        val l = typeLValue(lhs)
        val r = typeExpr(rhs)
        l match {
          case m: MemberMethod =>
            issue(new AssignMethodError(m.method.name, stmt.pos))
          case m: StaticMethod =>
            issue(new AssignMethodError(m.method.name, stmt.pos))
          case v: LocalVar =>
            // if (ctx.currentScope.isLambda && v.variable.domain.isLocal && v.variable.domain != ctx.currentScope)

            // printf(s"Assign a local var:\n domain = ${v.variable.domain},\n scopes = ${ctx.scopes.mkString("\n")}\nEndAssign\n")

            if (ctx.currentScope.isLambda && v.variable.domain.isLocal && !checkSameLocal(
                  v.variable.domain,
                  ctx.scopes
                ))
              issue(new AssCapturedError(stmt.pos))
          case _ =>
        }
        l.typ match {
          case NoType => // do nothing
          case t if !(r.typ <= t) =>
            issue(new IncompatBinOpError("=", l.typ, r.typ, stmt.pos))
          case _ => // do nothing
        }
        (Assign(l, r), EmptyType, false)

      case ExprEval(expr) =>
        val e = typeExpr(expr)
        (ExprEval(e), EmptyType, false)

      case Skip() => (Skip(), EmptyType, false)

      case If(cond, trueBranch, falseBranch) =>
        val c = checkTestExpr(cond)
        val (t, trueReturnType, trueReturns) = checkBlock(trueBranch)
        val (f, rt, r) = falseBranch.map(checkBlock) match {
          case Some((fb, falseBranchType, falseReturns)) =>
            // printf(s"At ${stmt.pos}, the 'If stmt' has two branches, trueReturns = $trueReturns, falseReturns = $falseReturns\n")

            (
              Some(fb),
              typeUpperBound2(trueReturnType, falseBranchType),
              trueReturns && falseReturns
            )
          case None => (None, trueReturnType, false)
        }

        // printf(s"At ${stmt.pos}, An 'If stmt', returnType = ${rt}, returns = $r\n")

        (If(c, t, f), rt, r)

      case While(cond, body) =>
        val c = checkTestExpr(cond)
        val (b, rt, _) = checkBlock(body)(ctx, insideLoop = true)
        (While(c, b), rt, false)

      case For(init, cond, update, body) =>
        // Since `init` and `update` may declare local variables, remember to first open the local scope of `body`.
        val local = ctx.open(body.scope)
        val (i, crt, cr) = checkStmt(init)(local, insideLoop)
        val c = checkTestExpr(cond)(local)
        val (u, urt, _) = checkStmt(update)(local, insideLoop)
        val ss = body.stmts.map { checkStmt(_)(local, insideLoop = true) }
        val bodyReturnTypes = ss.filter(_._2 != EmptyType).map(_._2)
        val (bodyReturnType, returns) = bodyReturnTypes.length match {
          case 0 => (EmptyType, false)
          case 1 => (bodyReturnTypes.head, true)
          case _ => (bodyReturnTypes.reduce(typeUpperBound2 _), true)
        }
        val b = Block(ss.map(_._1))(body.scope)
        (For(i, c, u, b), typeUpperBound(List(crt, urt, bodyReturnType)), cr)

      case Break() =>
        if (!insideLoop) issue(new BreakOutOfLoopError(stmt.pos))
        (Break(), EmptyType, false)

      case Return(expr) =>
        val e = expr match {
          case Some(e1) => Some(typeExpr(e1))
          case None     => None
        }
        val actual = e.map(_.typ).getOrElse(VoidType)
        if (!ctx.currentScope.isLambda) {
          // printf(s"Return:\n ctx.currentMethod = ${ctx.currentMethod}\n")
          // printf(s"ctx.currentMethod.typ = ${ctx.currentMethod.typ}")
          // printf(s"ctx.currentMethod.typ.ret = ${ctx.currentMethod.typ.ret}")

          val expected = ctx.currentMethod.typ.ret
          if (actual.noError && !(actual <= expected))
            issue(new BadReturnTypeError(expected, actual, stmt.pos))
        }
        (Return(e), actual, true)

      case Print(exprs) =>
        val es = exprs.zipWithIndex.map {
          case (expr, i) =>
            val e = typeExpr(expr)
            if (e.typ.noError && !e.typ.isBaseType)
              issue(new BadPrintArgError(i + 1, e.typ, expr.pos))
            e
        }
        (Print(es), EmptyType, false)
    }

    checked match {
      case (s, rt, r) => (s.setPos(stmt.pos), rt, r)
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
    // printf(s"testExpr(expr = $expr) at ${expr.pos}\n")

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
        val expr = ExpressionLambda(params, re, scope)(typ)
        scope.owner.asInstanceOf[LambdaSymbol].typ = typ
        expr

      case BlockLambda(params, block, scope) =>
        val fctx = ctx.open(scope)
        val lctx = fctx.open(scope.nestedScope)
        var (b, retTyp, returns) = checkBlock(block)(lctx)

        if (retTyp == EmptyType) retTyp = VoidType

        var typ = FunType(params.map(_.typeLit.typ), retTyp)

        // printf(s"At ${expr.pos}, Type BlockLambda (retTyp = $retTyp, returns = $returns)\n")

        if (!retTyp.isVoidType && !returns)
          issue(new MissingReturnError(block.pos))
        if (retTyp == NoType) issue(new TypeIncompError(block.pos))

        val expr = BlockLambda(params, b, scope)(typ)
        scope.owner.asInstanceOf[LambdaSymbol].typ = typ
        expr

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
            ArrayLenCall(r.get)(IntType)

          case Some(t @ ClassType(c, _)) =>
            ctx.global(c).scope.lookup(method) match {
              case Some(sym) =>
                sym match {
                  case m: MethodSymbol => typeCall(call, r, m)
                  case v: MemberVarSymbol =>
                    v.typ match {
                      case FunType(typArgs, ret) =>
                        if (typArgs.length != args.length) {
                          issue(
                            new BadArgCountError(
                              v.name,
                              typArgs.length,
                              args.length,
                              expr.pos
                            )
                          )
                        }
                        val as = (typArgs zip args).zipWithIndex.map {
                          case ((t, a), i) =>
                            val e = typeExpr(a)
                            if (e.typ.noError && !(e.typ <= t)) {
                              issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                            }
                            e
                        }
                        // TODO: fix this cheat¦
                        // Q on 2019-12-20: What's cheat? What am I writing?
                        FunctionCall(MemberVar(This(), v)(v.typ), as)(ret)
                      case NoType => err
                      case _ =>
                        issue(new CallUncallableError(v.typ, expr.pos))
                        err
                    }
                  case _ =>
                    issue(new NotClassMethodError(method, t, method.pos)); err
                }
              case None =>
                if (receiver == None) {
                  issue(new UndeclVarError(method.name, method.pos)); err
                } else {
                  issue(new FieldNotFoundError(method.name, t, method.pos)); err
                }
            }
          case None =>
            ctx.lookupBefore(method, method.pos) match {
              case Some(sym) if !initVars.contains(sym.name) =>
                sym match {
                  case v: LocalVarSymbol =>
                    v.typ match {
                      case FunType(typArgs, ret) =>
                        if (typArgs.length != args.length) {
                          issue(
                            new BadArgCountError(
                              v.name,
                              typArgs.length,
                              args.length,
                              expr.pos
                            )
                          )
                        }
                        val as = (typArgs zip args).zipWithIndex.map {
                          case ((t, a), i) =>
                            val e = typeExpr(a)
                            if (e.typ.noError && !(e.typ <= t)) {
                              issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                            }
                            e
                        }
                        
                        // printf(s"Try to capture ${v}\n")

                        ctx.capture(v)

                        FunctionCall(LocalVar(v)(v.typ), as)(ret)
                      case NoType => err
                      case _ =>
                        issue(new CallUncallableError(v.typ, expr.pos))
                        err
                    }
                  case v: MemberVarSymbol =>
                    v.typ match {
                      case FunType(typArgs, ret) =>
                        if (typArgs.length != args.length) {
                          issue(
                            new BadArgCountError(
                              v.name,
                              typArgs.length,
                              args.length,
                              expr.pos
                            )
                          )
                        }
                        val as = (typArgs zip args).zipWithIndex.map {
                          case ((t, a), i) =>
                            val e = typeExpr(a)
                            if (e.typ.noError && !(e.typ <= t)) {
                              issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                            }
                            e
                        }
                        // TODO: fix this cheat¦
                        // Q on 2019-12-20: What's cheat? What am I writing?
                        FunctionCall(MemberVar(This(), v)(v.typ), as)(ret)
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
                          issue(
                            new BadArgCountError(
                              m.name,
                              typArgs.length,
                              args.length,
                              expr.pos
                            )
                          )
                        }
                        val as = (typArgs zip args).zipWithIndex.map {
                          case ((t, a), i) =>
                            val e = typeExpr(a)
                            if (e.typ.noError && !(e.typ <= t)) {
                              issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                            }
                            e
                        }

                        if (m.isStatic) {
                          StaticCall(m, as)(ret)
                        } else {
                          MemberCall(This(), m, as)(ret)
                        }
                    }
                  case _ =>
                    issue(new UndeclVarError(method, method.pos)); err
                }
              case _ => issue(new UndeclVarError(method, method.pos)); err
            }
          case Some(t) =>
            issue(new NotClassFieldError(method, t, method.pos)); err
        }

      case call @ Call(func, args) =>
        val f = typeExpr(func)
        f.typ match {
          case NoType => err
          case FunType(typArgs, ret) =>
            if (typArgs.length != args.length) {
              issue(
                new LambdaBadArgCountError(
                  typArgs.length,
                  args.length,
                  expr.pos
                )
              )
            }
            var as = (typArgs zip args).zipWithIndex.map {
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
    // printf(s"At ${expr.pos}, typeLValue(expr = $expr)\n")

    val err = ErrorTypeLValue(expr)

    val typed = expr match {
      // Variable, which should be complicated since a legal variable could refer to a local var,
      // a visible member var (, and a class name).
      case VarSel(None, id) =>
        // printf("VarSel(None, " + id.name + ")\n")

        // Be careful we may be inside the initializer, if so, load the correct "before position".
        // TODO: [[if identifier != id]]
        ctx.lookupBefore(id, id.pos) match {
          case Some(sym) if !initVars.contains(sym.name) =>
            sym match {
              case v: LocalVarSymbol =>
                // printf(s"Try to capture ${v}\n")

                ctx.capture(v)

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
                // printf(
                //   s"Find a MethodSymbol $m, m.isStatic = ${m.isStatic}, ctx.currentMethod.isStatic = ${ctx.currentMethod.isStatic}\n"
                // )

                if (!m.isStatic) // member vars cannot be accessed in a static method
                  {
                    if (ctx.currentMethod.isStatic) {
                      issue(
                        new RefNonStaticError(
                          id,
                          ctx.currentMethod.name,
                          expr.pos
                        )
                      )
                    }

                //   printf(s"It's a member method!\n")

                    MemberMethod(This(), m)(m.typ)
                  } else {

                //   printf(s"It's a static method!\n")

                  StaticMethod(ctx.currentClass, m)(m.typ)
                }
              case _ =>
                // printf("When typeChecking VarSel " + id.name + ", we find a strange symbol.\n")

                issue(new UndeclVarError(id, expr.pos)); err
            }
          case _ =>
            // printf("VarSel fail to find " + id.name + ".\n")

            issue(new UndeclVarError(id, expr.pos)); err
        }

      case VarSel(Some(VarSel(None, id)), f) if ctx.global.contains(id) =>
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
          case ArrayType(elemType)
              if id.name == "length" => // Special case: array.length
            ArrayLen(r)(FunType(List(), elemType))
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
                    if (m.isStatic) { // TODO: Some unknown issue should occur here
                        StaticMethod(m.owner, m)(m.typ)
                    }
                    else {
                        MemberMethod(r, m)(m.typ)
                    }
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

  private val initVars: mutable.TreeSet[String] = new mutable.TreeSet

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
