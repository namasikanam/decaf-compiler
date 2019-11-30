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
      case NoType => Typed.TError()(NoType)
      case NullType => Typed.TNull()(NullType)
      case t @ FunType(args, ret) =>
        Typed.TLambda(fromTypeToTypeLit(ret), args.map(fromTypeToTypeLit))(t)
    }
  }

  def typeUpperBound(tl: List[Type]): Type = tl.reduce(typeUpperBound2)

  def typeUpperBound2(_t1: Type, _t2: Type): Type = {
      (_t1, _t2) match {
          case (NoType, _) | (_, NoType) => NoType
          case (NullType, NullType) => NullType
          case (EmptyType, t2) => t2
          case (t1, EmptyType) => t1
          case _ =>
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
                    case IntType | StringType | BoolType | VoidType | ArrayType(_) | ClassType(_, None) => NoType
                    case ClassType(_, Some(p)) => typeUpperBound2(p, t2)
                    case FunType(args1, ret1) => t2 match {
                        case FunType(args2, ret2) if args1.length == args2.length =>
                        val t = FunType((args1 zip args2).map(x => typeLowerBound2(x._1, x._2)), typeUpperBound2(ret1, ret2))
                        if (!t.args.filter(_ == NoType).isEmpty || t.ret == NoType) NoType
                        else t
                        case _ => NoType
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
                case IntType | StringType | BoolType | VoidType | ArrayType(_) | ClassType(_, None) => NoType
                case ClassType(_, Some(p)) => typeLowerBound2(p, t2)
                case FunType(args1, ret1) => t2 match {
                    case FunType(args2, ret2) if args1.length == args2.length =>
                        val t = FunType((args1 zip args2).map(x => typeUpperBound2(x._1, x._2)), typeLowerBound2(ret1, ret2))
                        if (!t.args.filter(_ == NoType).isEmpty || t.ret == NoType) NoType
                        else t
                    case _ => NoType
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
}