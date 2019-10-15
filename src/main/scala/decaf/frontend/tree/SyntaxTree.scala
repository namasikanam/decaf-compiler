package decaf.frontend.tree

import decaf.frontend.annot.Annot
import decaf.frontend.tree.TreeNode.Id

/**
  * A syntax tree, with no annotations.
  *
  * @see [[TreeTmpl]]
  */
object SyntaxTree extends TreeTmpl {

  /**
    * Dummy annotation.
    *
    * Here we made a dummy annotation to act as a placeholder for the `annot` field, and we made it implicit.
    * In this way, we can simply write:
    * {{{ VarSel(r, v) }}}
    * to create a `VarSel` node, because the Scala compiler will expand it to:
    * {{{ VarSel(r, v)(NoAnnot) }}}
    */
  implicit object NoAnnot extends Annot {

    override def toString: String = ""
  }

  type No = NoAnnot.type

  type TopLevelAnnot = No
  type ClassAnnot = No
  type MemberVarAnnot = No
  type LocalVarAnnot = No
  type MethodAnnot = No
  type TypeLitAnnot = No
  type StmtAnnot = No
  type BlockAnnot = No
  type ExprAnnot = No

  type ClassRef = Id

  // The following nodes only appear in a syntax tree.

  /**
    * Field selection, or simply a local variable.
    * {{{
    *   (receiver '.')? variable
    * }}}
    *
    * @param receiver target instance
    * @param variable identifier of the selected variable
    */
  case class VarSel(receiver: Option[Expr], variable: Id)(
      implicit val annot: ExprAnnot
  ) extends LValue {

    def withReceiver(receiver: Expr): VarSel =
      VarSel(Some(receiver), variable)(annot).setPos(pos)
  }

  /**
    * Call.
    * {{{
    *   expr '(' expr1 ','  expr2 ',' ... ')'
    * }}}
    *
    * @param expr       called method
    * @param exprList   a list of expressions as arguments
    */
  case class Call(expr: Expr, exprList: List[Expr])(
      implicit val annot: ExprAnnot
  ) extends Expr

}
