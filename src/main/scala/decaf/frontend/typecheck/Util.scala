package decaf.frontend.typecheck

import decaf.driver.error._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.tree.SyntaxTree._
import decaf.frontend.tree.TreeNode._
import decaf.frontend.tree.{TypedTree => Typed}

/**
  * Type checking shared utilities.
  */
trait Util extends ErrorIssuer {

  /**
    * Type check a type literal.
    *
    * @param typeLit type literal
    * @param ctx     scope context
    * @return a typed type literal
    */
  def typeTypeLit(
      typeLit: TypeLit
  )(implicit ctx: ScopeContext): Typed.TypeLit = {
    val typed = typeLit match {
      case TInt()    => Typed.TInt()(IntType)
      case TBool()   => Typed.TBool()(BoolType)
      case TString() => Typed.TString()(StringType)
      case TVoid()   => Typed.TVoid()(VoidType)
      case TVar()    => Typed.TVar()(VarType)

      case TClass(id) =>
        ctx.global.find(id.name) match {
          case Some(clazz) => Typed.TClass(clazz)(clazz.typ)
          case None =>
            issue(new ClassNotFoundError(id.name, typeLit.pos));
            Typed.TVoid()(VoidType)
        }

      case TArray(elemType) =>
        val typedElemType = typeTypeLit(elemType)
        val typ = typedElemType.typ match {
          case NoType   => NoType // avoid nested errors
          case VoidType => issue(new BadArrElementError(typeLit.pos)); NoType
          case t        => ArrayType(t)
        }
        Typed.TArray(typedElemType)(typ)
      
        case TLambda(returnType, typeList) =>
          val ret = typeTypeLit(returnType)
          val tl = typeList.map(typeTypeLit)
          if (tl.map(t => t match {
              case Typed.TVoid() =>
                issue(new VoidArgError(t.pos)); false
              case Typed.TVoidArgLambda() => false
              case _ => true
          }).fold(true)(_ && _))
            Typed.TLambda(ret, tl)(FunType(tl.map(t => t.typ), ret.typ))
          else
            Typed.TVoidArgLambda()(NoType)
    }
    typed.setPos(typeLit.pos)
  }

  /**
    * Transform a [Type] to a [TypeLit]
    * No type check here.
    *
    * @param typ a [Type]
    * @return a [TypeLit]
    */
  def fromTypeToTypeLit(
      typ: Type
  )(implicit ctx: ScopeContext): Typed.TypeLit = {
    typ match {
      case IntType                     => Typed.TInt()(IntType)
      case BoolType                    => Typed.TBool()(BoolType)
      case StringType                  => Typed.TString()(StringType)
      case t @ ClassType(name, parent) => Typed.TClass(ctx.global(name))(t)
      case t @ ArrayType(elemType) =>
        Typed.TArray(fromTypeToTypeLit(elemType))(t)
      case VoidType => Typed.TVoid()(VoidType)
      case VarType  => Typed.TVar()(VarType)
      case NoType =>
        Typed.TVar()(VarType) // I'm not sure here, it's supposed to be not going to happen
      case NullType => Typed.TNull()(NullType)
      case t @ FunType(args, ret) =>
        Typed.TLambda(fromTypeToTypeLit(ret), args.map(fromTypeToTypeLit))(t)
    }
  }

  def typeUpperBound(tl: List[Type]): Type = tl.reduce(typeUpperBound2)

  def typeUpperBound2(_t1: Type, _t2: Type): Type = {
      if (_t1 == NoType || _t2 == NoType) NoType
      else if (_t1 == NullType && _t2 == NullType) NullType
      else {
        var t1: Type = NoType
        var t2: Type = NoType
        if (t1 == NullType) {
            t1 = _t2
            t2 = _t1
        }
        else {
            t1 = _t1
            t2 = _t2
        }
        if (t2 <= t1) t1
        else {
            t1 match {
                case IntType | StringType | BoolType | VoidType | ArrayType(_) | ClassType(_, None) | NoType =>
                    issue(new TypeIncompError(t1, t2)); NoType
                case ClassType(_, Some(p)) => typeUpperBound2(p, t2)
                case FunType(args1, ret1) => t2 match {
                    case FunType(args2, ret2) if args1.length == args2.length =>
                        FunType((args1 zip args2).map(x => typeUpperBound2(x._1, x._2)), typeLowerBound2(ret1, ret2))
                    case _ => issue(new TypeIncompError(t1, t2)); NoType
                }
            }
        }
      }
  }
  
  def typeLowerBound(tl: List[Type]): Type = tl.reduce(typeLowerBound2)

  def typeLowerBound2(_t1: Type, _t2: Type): Type = {
      if (_t1 == NoType || _t2 == NoType) NoType
      else if (_t1 == NullType && _t2 == NullType) NullType
      else {
        var t1: Type = NoType
        var t2: Type = NoType
        if (t1 == NullType) {
            t1 = _t2
            t2 = _t1
        }
        else {
            t1 = _t1
            t2 = _t2
        }
        if (t1 <= t2) t1
        else {
            t1 match {
                case IntType | StringType | BoolType | VoidType | ArrayType(_) | ClassType(_, None) | NoType =>
                    issue(new TypeIncompError(t1, t2)); NoType
                case ClassType(_, Some(p)) => typeLowerBound2(p, t2)
                case FunType(args1, ret1) => t2 match {
                    case FunType(args2, ret2) if args1.length == args2.length =>
                        FunType((args1 zip args2).map(x => typeLowerBound2(x._1, x._2)), typeUpperBound2(ret1, ret2))
                    case _ => issue(new TypeIncompError(t1, t2)); NoType
                }
            }
        }
      }
  }

  def checkSameLocal(domain: Scope, scopes: List[Scope]): Boolean = {
    if (scopes.head.isFormal) false
    else {
        if (domain == scopes.head) true
        else {
            // printf(s"Not equal:\n domain = ${domain}, scopes.last = ${scopes.last}\n")
            checkSameLocal(domain, scopes.tail)
        }
    }
  }

  def resolveLocalVarDef(v: LocalVarDef)(
      implicit ctx: ScopeContext,
      isParam: Boolean = false
  ): Option[Typed.LocalVarDef] = {
    ctx.findConflictBefore(v.name, v.pos) match {
      case Some(earlier) =>
        printf(s"At ${v.pos}, DeclConflictError occurs when resolving LocalVarDef\n")

        issue(new DeclConflictError(v.name, earlier.pos, v.pos))
        // NOTE: when type check a method, even though this parameter is conflicting, we still need to know what is the
        // type. Suppose this type is ok, we can still construct the full method type signature, to the user's
        // expectation.
        if (isParam) {
          val typedTypeLit = typeTypeLit(v.typeLit)
          Some(
            Typed.LocalVarDef(
              typedTypeLit,
              v.id,
              v.init,
              v.assignPos
            )(null)
          )
        } else {
          // Remain lambda, but do not to declare
          // Append the id with a random string for convenience
          None
        }
      case None =>
        printf(s"At ${v.pos}, here's no conflict with ${v.name}!\n")

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
                v.init,
                v.assignPos
              )(symbol)
            )
        }
    }
  }
}