package decaf.driver.error

import decaf.frontend.annot.{ClassType, Type}
import decaf.frontend.parsing.{NoPos, Pos}

/**
  * Decaf error.
  *
  * @param msg error message
  * @param pos error position
  */
abstract class Error(val msg: String, val pos: Pos = NoPos) extends Exception {

  override def toString: String = pos match {
    case NoPos => s"*** Error: $msg"
    case _     => s"*** Error at (${pos.line},${pos.column}): $msg"
  }
}

// Lexer errors

case class NewlineInStrError(literal: String, override val pos: Pos)
    extends Error(s"illegal newline in string constant $literal", pos)

case class UntermStrError(literal: String, override val pos: Pos)
    extends Error(s"unterminated string constant $literal", pos)

case class UnrecogCharError(char: Char, override val pos: Pos)
    extends Error(s"unrecognized character '$char'", pos)

case class IntTooLargeError(literal: String, override val pos: Pos)
    extends Error(s"integer literal $literal is too large", pos)

/**
  * Lexer error: illegal escape character.
  *
  * Decaf only support the following escape characters: `\n`, `\t`, `\r`, `\"`, and `\\`. Others like `\a` are illegal.
  *
  * @example
  * {{{
  * illegal escape character:
  * str = "\a";
  * ^
  * }}}
  **/
case class BadEscCharError(override val pos: Pos) extends Error("illegal escape character", pos)

// Syntax error

case class SyntaxError(override val pos: Pos) extends Error("syntax error", pos)

// Namer errors

case class BadArrElementError(override val pos: Pos)
    extends Error("array element type must be non-void known type", pos)

case class BadVarTypeError(id: String, override val pos: Pos)
    extends Error(s"cannot declare identifier '$id' as void type", pos)

case class BadInheritanceError(override val pos: Pos)
    extends Error("illegal class inheritance (should be acyclic)", pos)

case class BadOverrideError(fun: String, parent: String, override val pos: Pos)
    extends Error(
      s"overriding method '$fun' doesn't match the type signature in class '$parent'",
      pos
    )

case class OverridingVarError(id: String, override val pos: Pos)
    extends Error(s"overriding variable is not allowed for var '$id'", pos)

case class ClassNotFoundError(clazz: String, override val pos: Pos)
    extends Error(s"class '$clazz' not found", pos)

case class DeclConflictError(id: String, earlier: Pos, override val pos: Pos)
    extends Error(
      s"declaration of '$id' here conflicts with earlier declaration at " +
        s"(${earlier.line},${earlier.column})",
      pos
    )

case object NoMainClassError
    extends Error("no legal Main class named 'Main' was found")

case class AbstractOverrideError(id: String, override val pos: Pos)
    extends Error(
      s"'$id' is not abstract and does not override all abstract methods",
      pos
    )

// Typer errors

case class BreakOutOfLoopError(override val pos: Pos)
    extends Error("'break' is only allowed inside a loop", pos)

case class BadTestExpr(override val pos: Pos)
    extends Error("test expression must have bool type", pos)

case class BadPrintArgError(k: Int, actual: Type, override val pos: Pos)
    extends Error(
      s"incompatible argument $k: $actual given, int/bool/string expected",
      pos
    )

case class BadReturnTypeError(expected: Type, actual: Type, override val pos: Pos)
    extends Error(
      s"incompatible return: $actual given, $expected expected",
      pos
    )

case class MissingReturnError(override val pos: Pos)
    extends Error(
      "missing return statement: control reaches end of non-void block",
      pos
    )

case class IncompatUnOpError(op: String, exprType: Type, override val pos: Pos)
    extends Error(s"incompatible operand: $op $exprType", pos)

case class IncompatBinOpError(op: String, lhsType: Type, rhsType: Type, override val pos: Pos)
    extends Error(s"incompatible operands: $lhsType $op $rhsType", pos)

case class NotArrayError(override val pos: Pos)
    extends Error("[] can only be applied to arrays", pos)

case class SubNotIntError(override val pos: Pos)
    extends Error("array subscript must be an integer", pos)

case class BadNewArrayLength(override val pos: Pos)
    extends Error("new array length must be an integer", pos)

case class ThisInStaticFuncError(override val pos: Pos)
    extends Error("can not use this in static function", pos)

case class UndeclVarError(v: String, override val pos: Pos)
    extends Error(s"undeclared variable '$v'", pos)

case class NotClassError(typ: Type, override val pos: Pos)
    extends Error(s"$typ is not a class type", pos)

case class FieldNotFoundError(field: String, clazz: ClassType, override val pos: Pos)
    extends Error(s"field '$field' not found in '$clazz'", pos)

case class FieldNotAccessError(field: String, clazz: ClassType, override val pos: Pos)
    extends Error(s"field '$field' of '$clazz' not accessible here", pos)

case class RefNonStaticError(field: String, method: String, override val pos: Pos)
    extends Error(
      s"can not reference a non-static field '$field' from static method '$method'",
      pos
    )

case class NotClassFieldError(field: String, typ: Type, override val pos: Pos)
    extends Error(s"cannot access field '$field' from '$typ'", pos)

case class NotClassMethodError(field: String, clazz: ClassType, override val pos: Pos)
    extends Error(s"'$field' is not a method in class '$clazz'", pos)

case class BadArgCountError(method: String, expected: Int, actual: Int, override val pos: Pos)
    extends Error(
      s"function '$method' expects $expected argument(s) but $actual given",
      pos
    )

case class BadArgTypeError(k: Int, expected: Type, actual: Type, override val pos: Pos)
    extends Error(
      s"incompatible argument $k: $actual given, $expected expected",
      pos
    )

case class BadLengthArgError(count: Int, override val pos: Pos)
    extends Error(
      s"function 'length' expects 0 argument(s) but $count given",
      pos
    )

case class NewAbstractError(clazz: String, override val pos: Pos)
    extends Error(s"cannot instantiate abstract class '$clazz'", pos)

case class CallUncallableError(typ: Type, override val pos: Pos)
    extends Error(s"$typ is not a callable type", pos)

case class DeclVoidTypeError(id: String, override val pos: Pos)
    extends Error(s"cannot declare identifier '$id' as void type", pos)

case class LambdaBadArgCountError(expected: Int, actual: Int, override val pos: Pos)
    extends Error(
      s"lambda expression expects $expected argument(s) but $actual given",
      pos
    )

// TODO: what's exact output of this?
case class TypeIncompError(override val pos: Pos) extends Error(s"incompatible return types in blocked expression.", pos)

case class VoidArgError(override val pos: Pos) extends Error(s"arguments in function type must be non-void known type", pos)

case class AssignMethodError(name: String, override val pos: Pos) extends Error(s"cannot assign value to class member method '$name'", pos)

case class AssCapturedError(override val pos: Pos) extends Error(s"cannot assign value to captured variables in lambda expression", pos)