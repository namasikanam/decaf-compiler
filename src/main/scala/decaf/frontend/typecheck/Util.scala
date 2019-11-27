package decaf.frontend.typecheck

import decaf.driver.error._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.tree.SyntaxTree._
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
}
