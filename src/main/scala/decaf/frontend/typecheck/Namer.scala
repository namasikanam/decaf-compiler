package decaf.frontend.typecheck

import decaf.driver.error._
import decaf.driver.{Config, Phase}
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.parsing._
import decaf.frontend.tree.SyntaxTree._
import decaf.frontend.tree.TreeNode._
import decaf.frontend.tree.{TypedTree => Typed}

import scala.collection.mutable

/**
  * The namer phase: resolve all symbols defined in the abstract syntax tree and store them in symbol tables (i.e.
  * scopes).
  *
  * ==Overview==
  * The entire type checking pass is split into two phases -- [[Namer]] and [[Typer]].
  *
  * Why two? Note that all defined classes are visible to every other class, which means we can access another
  * class's members, and of course the type that itself represents, e.g.
  * {{{
  * class A {
  *     class B foo; // access B
  *     void bar() {
  *         foo.baz(); // access baz of B
  *     }
  * }
  * class B {
  *     void baz();
  * }
  * }}}
  *
  * Apparently, classes cannot be resolved in the order they presented in the syntax tree: `A` refers to `B`,
  * whose definition goes '''later'''. To tackle this issue, one possible way is to first scan all classes ''roughly''
  * and then step into details of every method body -- because at that time, signatures of class members are known.
  *
  * In the [[Namer]] phase, we just scan all class members, while ignoring any statement/expressions which doesn't
  * define a new symbol (a variable), because that's enough for us to know what a class looks like.
  * After this phase, a '''not fully-typed''' tree is returned. In this tree:
  *
  *   - class and members are associated with their symbols (also the scopes)
  *   - methods are associated with their formal scopes (which contains symbols of parameters)
  *   - blocks are associated with their local scopes (which contains symbols of local variables)
  *
  * However, no typing checking has yet been done for any statement or expression.
  *
  * ===Implicit Contexts===
  * As you can see, implicits are widely-used in this project. I hope all of them are appropriate and not abused.
  * In particular, contexts are quite important and common in a type checking algorithm. However, since many times
  * contexts are passing to other functions without any change, specifying them are implicit parameters makes our
  * life easier -- we only need to explicitly pass them whenever they are updated, in very few situations!
  *
  * @see [[Typer]]
  * @see [[decaf.frontend.annot.Scope]]
  * @see [[decaf.frontend.annot.Symbol]]
  */
class Namer(implicit config: Config)
    extends Phase[Tree, Typed.Tree]("namer", config)
    with Util {

  class Context {

    val global: GlobalScope = new GlobalScope
    val classes: mutable.Map[String, ClassDef] = new mutable.TreeMap
  }

  /**
    * Transformer entry.
    *
    * @param tree an (untyped) abstract syntax tree
    * @return a typed tree with untyped holes
    */
  override def transform(tree: Tree): Typed.Tree = {
    implicit val ctx = new Context

    // Delete 'Main' decorated by 'abstract'
    tree.classes =
      tree.classes.filter(c => !(c.name == "Main" && c.modifiers.isAbstract));

    // Check conflicting definitions. If any, ignore the redefined ones.
    tree.classes.foreach { clazz =>
      ctx.classes.get(clazz.name) match {
        case Some(earlier) =>
          issue(new DeclConflictError(clazz.name, earlier.pos, clazz.pos))
        case None => ctx.classes(clazz.name) = clazz
      }
    }

    // Make sure the base class exists. If not, ignore the inheritance.
    ctx.classes.foreach {
      case (name, clazz) =>
        clazz.parent match {
          case Some(Id(base)) if !ctx.classes.contains(base) =>
            issue(new ClassNotFoundError(base, clazz.pos))
            ctx.classes(name) = clazz.parentDetached
          case _ =>
        }
    }

    // Make sure any inheritance does not form a cycle.
    checkCycles()
    // If so, return with errors.
    if (hasError) return Typed.TopLevel(Nil)(ctx.global)

    // So far, class inheritance is well-formed, i.e. inheritance relations form a forest of trees. Now we need to
    // resolve every class definition, make sure that every member (variables and methods) is well-typed.
    // Realizing that a class type can be used in the definition of a class member, either a variable or a method,
    // we shall first know all the accessible class types in the program. These types are wrapped into what we called
    // `ClassSymbol`s. Note that currently, the associated `scope` is empty because member resolving has not started
    // yet. All class symbols are stored in the global scope.
    createClassSymbols()

    // Now, we can resolve every class definition to fill in its class scope table. To check if the overriding
    // behaves correctly, we should first resolve super class and then its subclasses.
    val resolvedClasses = resolveClasses
    if (hasError) return Typed.TopLevel(Nil)(ctx.global)

    // Finally, let's locate the main class, whose name is 'Main', and contains a method like:
    //  static void main() { ... }
    resolvedClasses.find(_.name == "Main") match {
      case Some(clazz) =>
        clazz.symbol.scope.find("main") match {
          case Some(symbol) =>
            symbol match {
              case f: MethodSymbol
                  if f.isStatic && (f.typ === FunType(Nil, VoidType)) =>
                f.setMain()
              case _ => issue(NoMainClassError)
            }
          case _ => issue(NoMainClassError)
        }
      case None => issue(NoMainClassError)
    }
    if (hasError) return Typed.TopLevel(Nil)(ctx.global)

    printf("=======================Namer End===========================\n")

    Typed.TopLevel(resolvedClasses)(ctx.global).setPos(tree.pos)
  }

  /**
    * Check if class inheritance form cycle(s).
    */
  private def checkCycles()(implicit ctx: Context): Unit = {
    val visitedTime = new mutable.TreeMap[String, Int]
    ctx.classes.keys.foreach { visitedTime(_) = 0 }

    @scala.annotation.tailrec
    def visit(from: ClassDef, node: String, time: Int): Unit = {
      if (visitedTime(node) == 0) { // not visited yet
        visitedTime(node) = time
        val clazz = ctx.classes(node)
        clazz.parent match {
          case Some(Id(base)) => visit(clazz, base, time)
          case _              => // done
        }
      } else if (visitedTime(node) == time) { // find a cycle
        issue(new BadInheritanceError(from.pos))
        // ctx.classes(from.name) = from.parentDetached
      } // else: this node is visited earlier, also done
    }

    var time = 1
    for {
      node <- ctx.classes.keys
      if visitedTime(node) == 0
    } yield {
      visit(null, node, time)
      time += 1
    }
  }

  /**
    * Create class symbols and declare in the global scope.
    *
    * @param ctx context
    */
  private def createClassSymbols()(implicit ctx: Context): Unit = {
    def create(clazz: ClassDef): Unit = {
      if (!ctx.global.contains(clazz.name)) {
        val symbol = clazz.parent match {
          case Some(Id(base)) =>
            create(ctx.classes(base))
            val baseSymbol = ctx.global(base)
            val typ = ClassType(clazz.name, Some(baseSymbol.typ))
            val scope = new ClassScope(Some(baseSymbol.scope))
            new ClassSymbol(clazz, typ, scope, Some(baseSymbol))
          case None =>
            val typ = ClassType(clazz.name)
            val scope = new ClassScope()
            new ClassSymbol(clazz, typ, scope)
        }
        ctx.global.declare(symbol)
      }
    }

    ctx.classes.values.foreach(create)
  }

  /**
    * Resolve class definitions.
    * This a parameterless method,
    * which even parenthesises are omitted.
    *
    * @param ctx context
    * @return resolved classes
    */
  def resolveClasses(implicit ctx: Context): List[Typed.ClassDef] = {
    val resolved = new mutable.TreeMap[String, Typed.ClassDef]
    val abstractMethods =
      new mutable.TreeMap[String, Set[String]]

    def resolve(clazz: ClassDef): Unit = {
      if (!resolved.contains(clazz.name)) {
        clazz.parent match {
          case Some(Id(base)) => resolve(ctx.classes(base))
          case None           => ;
        }

        val symbol: ClassSymbol = ctx.global(clazz.name)

        // Resolve fields
        // Prepare implicit arguments first.
        implicit val classCtx: ScopeContext =
          new ScopeContext(ctx.global).open(symbol.scope)
        implicit val currentAbstractMethods: mutable.Set[String] =
          clazz.parent match {
            case Some(Id(base)) =>
              mutable.Set[String]() ++ abstractMethods(base)
            case None => mutable.Set[String]()
          }

        val fs = clazz.fields.flatMap(resolveField)
        if (!clazz.isAbstract && !currentAbstractMethods.isEmpty)
          issue(new AbstractOverrideError(clazz.id.name, clazz.pos))
        abstractMethods(clazz.name) = currentAbstractMethods.toSet

        resolved(clazz.name) =
          Typed.ClassDef(clazz.id, symbol.parent, fs)(symbol).setPos(clazz.pos)
      }
    }

    ctx.classes.values.foreach(resolve)
    ctx.classes.keys.map(resolved).toList
  }

  /**
    * Resolve a field definition.
    * A "field" of class contains the variables and methods defined in it.
    *
    * @param field field
    * @param ctx   scope context
    * @return resolved field
    */
  def resolveField(
      field: Field
  )(
      implicit ctx: ScopeContext,
      currentAbstractMethods: mutable.Set[String]
  ): Option[Typed.Field] = {
    val resolved = ctx.findConflict(field.name) match {
      case Some(earlier)
          if earlier.domain == ctx.currentScope => // always conflict
        issue(new DeclConflictError(field.name, earlier.pos, field.pos)); None
      case Some(earlier) => // maybe override?
        (earlier, field) match {
          case (_: MemberVarSymbol, _: VarDef) =>
            issue(new OverridingVarError(field.name, field.pos))
            None
          case (
              suspect: MethodSymbol,
              m @ MethodDef(mod, id, returnType, params, body)
              )
              if !suspect.isStatic && !m.isStatic && (!m.isAbstract || suspect.isAbstract) =>
            // Only non-static methods can be overriden, but the type signature must be equivalent.
            val ret = typeTypeLit(returnType)
            ret.typ match {
              case NoType => None
              case retType =>
                val formalScope = new FormalScope
                val formalCtx = ctx.open(formalScope)
                if (!m.isStatic)
                  formalCtx.declare(
                    LocalVarSymbol.thisVar(ctx.currentClass.typ, id.pos)
                  )
                val typedParams = params.flatMap {
                  resolveLocalVarDef(_)(formalCtx, true)
                }
                val funType = FunType(typedParams.map(_.typeLit.typ), retType)
                if (funType <= suspect.typ) { // override success
                  // Maintain the set of abstract methods
                  if (suspect.isAbstract && !m.isAbstract)
                    currentAbstractMethods -= suspect.name

                  val symbol =
                    new MethodSymbol(m, funType, formalScope, ctx.currentClass)
                  ctx.declare(symbol)
                  val block = resolveBlock(body)(formalCtx)
                  Some(
                    Typed.MethodDef(mod, id, ret, typedParams, block)(symbol)
                  )
                } else { // override failure
                  issue(new BadOverrideError(m.name, suspect.owner.name, m.pos))
                  None
                }
            }
          case _ =>
            issue(new DeclConflictError(field.name, earlier.pos, field.pos));
            None
        }
      case None =>
        field match {
          case v @ VarDef(typeLit, id) =>
            val lit = typeTypeLit(typeLit)
            lit.typ match {
              case NoType => None
              case VoidType =>
                v.typeLit match {
                    case TVoid() => issue(new BadVarTypeError(v.name, v.pos))
                    case _ =>
                }
                None
              case t =>
                val symbol = new MemberVarSymbol(v, t, ctx.currentClass)
                ctx.declare(symbol)
                Some(Typed.VarDef(lit, id)(symbol))
            }
          case m @ MethodDef(mod, id, returnType, params, body) =>
            val rt = typeTypeLit(returnType)
            val retType = rt.typ
            var formalScope = new FormalScope
            formalScope.nestedScope = new LocalScope
            val formalCtx: ScopeContext = ctx.open(formalScope)

            if (!m.isStatic)
              formalCtx.declare(
                LocalVarSymbol.thisVar(ctx.currentClass.typ, id.pos)
              )
            if (m.isAbstract) currentAbstractMethods += m.name

            val typedParams = params.flatMap {
              resolveLocalVarDef(_)(formalCtx, true)
            }
            val funType = FunType(typedParams.map(_.typeLit.typ), retType)
            val symbol =
              new MethodSymbol(m, funType, formalScope, ctx.currentClass)
            
            printf(s"Build MethodSymbol: the ownerMethod of scope of MethodSymbol $symbol is ${symbol.scope.ownerMethod}\n")

            ctx.declare(symbol)
            val block = resolveBlock(body)(formalCtx)
            Some(Typed.MethodDef(mod, id, rt, typedParams, block)(symbol))
        }
    }
    resolved.map(_.setPos(field.pos))
  }

  /**
    * Resolve a statement block.
    *
    * @param block statement block
    * @param ctx   scope context
    * @return resolved block
    */
  def resolveBlock(block: Block)(implicit ctx: ScopeContext): Typed.Block = {
    val localScope = new LocalScope
    ctx.currentScope match {
      case s: FormalScope =>
        s.nestedScope = localScope
      case s: LambdaScope =>
        localScope.lambdaFlag = true
        s.nestedScopes += localScope
      case s: LocalScope =>
        s.nestedScopes += localScope
    }
    val localCtx = ctx.open(localScope)
    val ss = block.stmts.map { resolveStmt(_)(localCtx) }
    Typed.Block(ss)(localScope).setPos(block.pos)
  }

  def resolveLValue(lValue: LValue)(implicit ctx: ScopeContext): Typed.LValue = {
    val resolved = (lValue match {
        case VarSel(None, id) => Typed.VarSel(None, id)(VarType)
        case VarSel(Some(receiver), id) => Typed.VarSel(Some(resolveExpr(receiver)), id)(VarType)
        case IndexSel(array, index) => Typed.IndexSel(resolveExpr(array), resolveExpr(index))(VarType)
    })
    resolved.setPos(lValue.pos)
  }

  // Build symbol in lambda expression
  def resolveExpr(expr: Expr)(implicit ctx: ScopeContext): Typed.Expr = {
    val err = Typed.ErrorSynExpr(expr)

    printf(s"At ${expr.pos}, resolveExpr $expr\n")

    val resolved = expr match {
        case e: LValue => resolveLValue(e)

        case IntLit(v) => Typed.IntLit(v)(IntType)
        case BoolLit(v) => Typed.BoolLit(v)(BoolType)
        case StringLit(v) => Typed.StringLit(v)(StringType)
        case NullLit() => Typed.NullLit()(NullType)

        case ReadInt() => Typed.ReadInt()(IntType)
        case ReadLine() => Typed.ReadLine()(StringType)

        case Unary(op, operand) => Typed.Unary(op, resolveExpr(operand))(VarType)

        case Binary(op, lhs, rhs) => Typed.Binary(op, resolveExpr(lhs), resolveExpr(rhs))(VarType)

        case ExpressionLambda(params, retExpr, formalScope) =>
            ctx.currentScope.asInstanceOf[LocalScope].nestedScopes += formalScope
            // open a formal scope and resolve all parameters of it
            formalScope.ownerMethod = ctx.currentMethod
            formalScope.lambdaFlag = true
            val formalCtx = ctx.open(formalScope)
            // resolve all parameters
            val ps = params.flatMap{resolveLocalVarDef(_)(formalCtx, true)}
            // open a nested lambda scope and resolve in it
            val lambdaScope = new LambdaScope
            formalScope.nestedScope = lambdaScope
            val lambdaCtx = formalCtx.open(lambdaScope)
            val re = resolveExpr(retExpr)(lambdaCtx)
            // Create and declare the symbol
            val typ = FunType(ps.map(_.typeLit.typ), VarType)
            val symbol = new LambdaSymbol(typ, formalScope, expr.pos)
            ctx.declare(symbol)
            Typed.ExpressionLambda(ps, re, formalScope)(typ)

        case BlockLambda(params, block, formalScope) =>
            ctx.currentScope.asInstanceOf[LocalScope].nestedScopes += formalScope
            // open a formal scope and resolve all parameters of it
            formalScope.ownerMethod = ctx.currentMethod
            formalScope.lambdaFlag = true
            val formalCtx = ctx.open(formalScope)
            val ps = params.flatMap{resolveLocalVarDef(_)(formalCtx, true)}
            // open a nested lambda scope and resolve in it
            val lambdaScope = new LambdaScope
            formalScope.nestedScope = lambdaScope
            val lambdaCtx = formalCtx.open(lambdaScope)
            val ss = block.stmts.map{ resolveStmt(_)(lambdaCtx) }
            // Create and declare the symbol
            val typ = FunType(ps.map(_.typeLit.typ), VarType)
            val symbol = new LambdaSymbol(typ, formalScope, expr.pos)
            val b = Typed.Block(ss)(lambdaScope).setPos(block.pos)
            ctx.declare(symbol)
            Typed.BlockLambda(ps, b, formalScope)(typ)

        case Call(fun, args) => Typed.Call(resolveExpr(fun), args.map(resolveExpr))(VarType)

        case ClassTest(obj, clazz) => Typed.UnTypedClassTest(resolveExpr(obj), clazz)(VarType)

        case ClassCast(obj, clazz) => Typed.UnTypedClassCast(resolveExpr(obj), clazz)(VarType)
        
        case NewArray(elemType, length) => Typed.UnTypedNewArray(typeTypeLit(elemType), resolveExpr(length))(VarType)

        case NewClass(id) => Typed.UnTypedNewClass(id)(VarType)

        case This() => Typed.This()(VarType)
    }
    
    resolved.setPos(expr.pos)
  }

  def resolveStmt(stmt: Stmt)(implicit ctx: ScopeContext): Typed.Stmt = {
    printf(s"At ${stmt.pos}, resolveStmt $stmt\n")

    val resolved = stmt match {
      case block: Block     => resolveBlock(block)
      case v: LocalVarDef   => resolveLocalVarDef(v) match {
        case Some(lv) => lv
        case None => Typed.Skip()
      }
      case Assign(lhs, rhs) => Typed.Assign(resolveLValue(lhs), resolveExpr(rhs))
      case ExprEval(expr)   => Typed.ExprEval(resolveExpr(expr))
      case Skip()           => Typed.Skip()
      case If(cond, trueBranch, falseBranch) =>
        val t = resolveBlock(trueBranch)
        val f = falseBranch.map(resolveBlock)
        Typed.If(resolveExpr(cond), t, f)
      case While(cond, body)             => Typed.While(resolveExpr(cond), resolveBlock(body))
      case For(init, cond, update, body) =>
        // Since `init` and `update` may declare local variables, we must first open the local scope of `body`, and
        // then resolve `init`, `update` and statements inside `body`.
        val localScope = new LocalScope
        ctx.currentScope.asInstanceOf[LocalScope].nestedScopes += localScope
        val localCtx = ctx.open(localScope)
        val i = resolveStmt(init)(localCtx)
        val c = resolveExpr(cond)(localCtx)
        val u = resolveStmt(update)(localCtx)
        val ss = body.stmts.map { resolveStmt(_)(localCtx) }
        val b = Typed.Block(ss)(localScope).setPos(body.pos)
        Typed.For(i, c, u, b)
      case Break()      => Typed.Break()
      case Return(someExpr) => Typed.Return(someExpr match{
          case Some(e) => Some(resolveExpr(e))
          case None => None
      })
      case Print(exprs) => Typed.Print(exprs.map(resolveExpr))
    }
    resolved.setPos(stmt.pos)
  }

  def resolveLocalVarDef(v: LocalVarDef)(
      implicit ctx: ScopeContext,
      isParam: Boolean = false
  ): Option[Typed.LocalVarDef] = {
    printf(s"resolveLocalVarDef $v\n")
    printf(s"initVars = $initVars\n")

    (ctx.findConflictBefore(v.name, v.pos) match {
        case Some(earlier) => Some(earlier.pos)
        case None => initVars.get(v.name)
    }) match {
      case Some(earlierPos) =>
        // printf(s"At ${v.pos}, DeclConflictError occurs when resolving LocalVarDef\n")

        issue(new DeclConflictError(v.name, earlierPos, v.pos))
        // NOTE: when type check a method, even though this parameter is conflicting, we still need to know what is the
        // type. Suppose this type is ok, we can still construct the full method type signature, to the user's
        // expectation.
        if (isParam) {
          val typedTypeLit = typeTypeLit(v.typeLit)
          Some(
            Typed.LocalVarDef(
              typedTypeLit,
              v.id,
              v.init.map(resolveExpr), // In fact, [[v.init]] must be [[None]] for a parameter. ResolveExpr for corret type.
              v.assignPos
            )(null)
          )
        } else {
            v.init.map(resolveExpr)
            None
        }
        case None =>
        initVars(v.name) = v.pos
        val init = v.init.map(resolveExpr)
        initVars -= v.name
        // printf(s"At ${v.pos}, here's no conflict with ${v.name}!\n")

        val typedTypeLit = typeTypeLit(v.typeLit)
        typedTypeLit.typ match {
          case NoType =>
            // NOTE: to avoid flushing a large number of error messages, if we know one error is caused by another,
            // then we shall not report both, but the earlier found one only. In this case, the error of the entire
            // LocalVarDef is caused by the bad typeLit, and thus we don't make further type check.
            None
          case VoidType =>
            v.typeLit match {
                case TVoid() => issue(new BadVarTypeError(v.name, v.pos))
                case _ =>
            }
            None
          case t =>
            val symbol = new LocalVarSymbol(v.name, t, v.pos)
            ctx.declare(symbol)
            
            // printf("declare name = " + symbol.name + "\n")

            Some(
              Typed.LocalVarDef(
                typedTypeLit,
                v.id,
                init,
                v.assignPos
              )(symbol)
            )
        }
    }
  }

  private val initVars: mutable.TreeMap[String, Pos] = new mutable.TreeMap
}