package decaf.frontend.annot

import decaf.frontend.parsing.Pos
import scala.collection.mutable
import decaf.driver.error._
import scala.sys
import scala.util.Random

/**
  * Scopes.
  *
  * A scope stores the mapping from names to symbols.
  *
  * @see [[GlobalScope]]
  * @see [[ClassScope]]
  * @see [[FormalScope]]
  * @see [[LocalScope]]
  */
sealed trait Scope extends Annot {

  /**
    * Type of stored symbols.
    */
  type Item <: Symbol

  /**
    * Is the scope (only the current one) empty?
    *
    * @return true if it is empty
    */
  def isEmpty: Boolean = symbols.isEmpty

  /**
    * Get all defined symbols in this scope, ordered by their positions.
    *
    * @return the list of symbols
    */
  def values: List[Item] = symbols.values.toList.sortBy(_.pos)

  /**
    * Does this scope contain a symbol named `key`?
    *
    * @param key symbol's name
    * @return true if this scope defines a symbol of that name
    */
  def contains(key: String): Boolean = symbols.contains(key)

  /**
    * Find a symbol with name `key`.
    *
    * @param key symbol's name
    * @return the matched symbol (if any)
    */
  def find(key: String): Option[Item] = symbols.get(key)

  /**
    * Get a symbol with name `key`.
    *
    * @see [[find]]
    *
    * @param key symbol's name
    * @return the matched symbol, or throws [[NoSuchElementException]] if not found
    */
  def apply(key: String): Item = symbols(key)

  /**
    * Apply the standard `flatMap` operation on all symbols defined in this scope.
    *
    * @param p collector of the `flatMap` operation
    * @tparam T result element type
    * @return a list of results
    */
  def flatMap[T](p: Item => Option[T]): List[T] =
    symbols.values.flatMap(p).toList

  /**
    * Declare a symbol in this scope.
    *
    * @param symbol symbol
    */
  def declare(symbol: Item): Unit = {
    symbols(symbol.name) = symbol
    symbol.domain = this
  }

  /** Is this a local or formal scope? */
  def isLocalOrFormal: Boolean = false

  /** Is this a formal scope? */
  def isFormal: Boolean = false

  /** Is this a local scope? */
  def isLocal: Boolean = false

  /** Is this a lambda scope? */
  var lambdaFlag = false
  def isLambda: Boolean = lambdaFlag

  override def toString: String =
    "{ " + (symbols.map {
      case (name, symbol) => s"  $name --> $symbol"
    } mkString "\n") + "\n(isFormal = " + (if (this.isFormal) "true"
                                           else
                                             "false") + ")" + " , " + "(isLambda = " + (if (this.isLambda)
                                                                                          "true"
                                                                                        else
                                                                                          "false") + ") , " + "(isLocal = " + (if (this.isLocal)
                                                                                                                                 "true"
                                                                                                                               else
                                                                                                                                 "false") + ") }"

  /**
    * Actual symbol table: maps names to their symbols.
    */
  var symbols: mutable.Map[String, Item] = new mutable.TreeMap
}

/**
  * Global scope: stores globally-defined class symbols.
  */
class GlobalScope extends Scope {

  type Item = ClassSymbol
}

/**
  * Class scope: stores symbols of class members.
  *
  * @param parent the scope of its super class (if any)
  */
class ClassScope(val parent: Option[ClassScope] = None) extends Scope {

  type Item = FieldSymbol

  /**
    * Lookup a symbol by name. Searches in all parent and ancestor scopes, and returns the innermost result.
    *
    * @param key symbol's name
    * @return innermost found symbol (if any)
    */
  def lookup(key: String): Option[FieldSymbol] = {
    // printf(s"lookup $key in $this\n")

    find(key).orElse(parent.flatMap(_.lookup(key)))
  }

  /**
    * Owner, a class symbol whose members are defined in this class scope.
    */
  var owner: ClassSymbol = _
}

/**
  * Formal scope: stores function parameter symbols.
  */
class FormalScope extends Scope {

  type Item = LocalVarSymbol

  override def isLocalOrFormal: Boolean = true

  override def isFormal: Boolean = true

  /**
    * The directly nested local scope of the function body.
    */
  var nestedScope: Scope = _

  /**
    * Owner, a method symbol whose parameters are defined in this formal scope,
    * which can be [[MethodSymbol]] or [[LambdaSymbol]]
    */
  var ownerMethod: MethodSymbol = _

  var owner: Symbol = _

  // This is only for the FormalScope of some lambda
  var captured: List[LocalVarSymbol] = List()
}

/**
  * Local scope: stores locally-defined variable symbol.
  */
class LocalScope extends Scope {

  type Item = Symbol

  override def isLocalOrFormal: Boolean = true

  override def isLocal: Boolean = true

  /**
    * Directly (possibly ''cross-level'') nested local scopes of this scope.
    *
    * For instance,
    * {{{
    *   { // block 1
    *     if (true) { // block 2
    *     }
    *   }
    * }}}
    * although block 2 is not a direct child of block 1, block 2 is still directly nested in block 1.
    */
  val nestedScopes: mutable.ArrayBuffer[Scope] =
    new mutable.ArrayBuffer[Scope]
}

/**
  * Lambda scope
  */
class LambdaScope extends LocalScope {
  lambdaFlag = true
}

/**
  * A symbol table, which is organized as a stack of scopes, maintained by [[decaf.frontend.typecheck.Namer]].
  *
  * A typical full scope stack looks like the following:
  * {{{
  *     LocalScope   --- stack top (current scope)
  *     ...          --- many nested local scopes
  *     LocalScope
  *     FormalScope
  *     ClassScope
  *     ...          --- many parent class scopes
  *     ClassScope
  *     GlobalScope  --- stack bottom
  * }}}
  * Make sure the global scope is always at the bottom, and NO class scope appears in neither formal nor local scope.
  *
  * @param global        the global scope at stack bottom
  * @param scopes        a list of scopes above the bottom (first is the top)
  * @param currentScope  the current scope
  * @param currentClass  the current class symbol, i.e. the owner of the latest class scope
  * @param currentMethod the current method symbol, i.e. owner of the latest formal scope
  * @see [[Scope]]
  */
class ScopeContext private (
    val global: GlobalScope,
    val scopes: List[Scope],
    val currentScope: Scope,
    val currentClass: ClassSymbol,
    val currentMethod: MethodSymbol
) {

  def this(globalScope: GlobalScope) =
    this(globalScope, Nil, globalScope, null, null)

  /**
    * Open a new scope.
    *
    * @param scope scope
    * @return a new scope context after opening `scope`
    */
  def open(scope: Scope): ScopeContext = {
    //   printf(s"Before open, ownerMethod = ${currentMethod}\n")
    //   printf(s"open scope $scope\n")

    scope match {
      case s: ClassScope =>
        s.parent match {
          case Some(ps) =>
            new ScopeContext(global, s :: open(ps).scopes, s, s.owner, null)
          case None => new ScopeContext(global, s :: scopes, s, s.owner, null)
        }
      case s: FormalScope =>
        if (s.isLambda)
          new ScopeContext(global, s :: scopes, s, currentClass, currentMethod)
        else {
          // printf(s"open a new method: ${s.ownerMethod}\n")

          new ScopeContext(global, s :: scopes, s, currentClass, s.ownerMethod)
        }
      case s: LocalScope =>
        new ScopeContext(global, s :: scopes, s, currentClass, currentMethod)
    }
  }

  /**
    * Find a symbol by name. Search in all possible scopes while the predicate `cond` holds, and the found symbol
    * satisfies `p`. Returns the innermost result.
    *
    * @param key    symbol's name
    * @param cond   the predicate over the currently visited scope
    * @param p      the predicate over the suspect symbol
    * @param scopes all remaining scopes to be searched
    * @return innermost found symbol (if any)
    */
  @scala.annotation.tailrec
  private def findWhile(
      key: String,
      cond: Scope => Boolean = _ => true,
      p: Symbol => Boolean = _ => true,
      scopes: List[Scope] = scopes :+ global
  ): Option[Symbol] =
    scopes match {
      case Nil => None
      case s :: ss =>
        if (!cond(s)) {
          None
        } else {
          //   printf(s"Find '$key' in scope $s\n")

          s.find(key) match {
            case Some(symbol) if p(symbol) =>
              // printf(s"Find '$key'!\n")

              Some(symbol)
            case _ =>
              // printf("Not found...\n")

              findWhile(key, cond, p, ss)
          }
        }
    }

  /**
    * Lookup a symbol by name. By saying "lookup", the user expects that the symbol is found.
    * In this way, we will always search in all possible scopes and returns the innermost result.
    *
    * @param key symbol's name
    * @return innermost found symbol (if any)
    */
  def lookup(key: String): Option[Symbol] = findWhile(key)

  /**
    * Same with [[lookup]] but we restrict the symbol's position to be before the given position.
    *
    * @param key symbol's name
    * @param pos position
    * @return innermost found symbol before `pos` (if any)
    */
  def lookupBefore(key: String, pos: Pos): Option[Symbol] = {
    // printf(s"lookupBefore($key, $pos)\n")

    findWhile(
      key,
      _ => true,
      s => !((s.domain.isLocalOrFormal || s.domain.isLambda) && s.pos >= pos)
    )
  }

  /**
    * Going back tracing the scope stack.
    * Similar with [[findWhile]].
    * Stop when meeting one of two conditions:
    * 1. This symbol is declared in the current scope
    * 2. The current lambda has captured this symbol
    * (The order of condition needs to be considered.)
    *
    * @param v symbol needs capturing
    * @param scopes the stack of scopes
    */
  def capture(v: LocalVarSymbol, scopes: List[Scope] = scopes): Unit = {
    scopes match {
      case Nil => None
      case s :: ss =>
        if (s.find(v.name).isEmpty) {
          s match {
            case fs: FormalScope =>
              if (!fs.captured.contains(v)) {
                // printf(s"FormalScope($fs).captured += LocalVarSymbol($v)\n")

                fs.captured = v +: fs.captured
                capture(v, ss)
              }
            case _ => capture(v, ss)
          }
        }
    }
  }

  /**
    * Find a symbol that conflicts with some already defined symbol. Rules:
    *
    *   - if the current scope is local scope or formal scope, `key` cannot conflict with any already defined symbol
    * up till the formal scope, and it cannot conflict with any names in the global scope
    *   - if the current scope is class scope or global scope, `key` cannot conflict with any already defined symbol
    *
    * NO override checking is performed here, the type checker should tell if the returned conflicting symbol is
    * in fact allowed or not.
    *
    * @param key symbol's name
    * @return innermost conflicting symbol (if any)
    */
  def findConflict(key: String): Option[Symbol] = currentScope match {
    case s if s.isLocalOrFormal =>
      findWhile(key, s => s.isLocalOrFormal || s.isLambda)
        .orElse(global.find(key))
    case _ => lookup(key)
  }

  def findConflictBefore(key: String, pos: Pos): Option[Symbol] =
    currentScope match {
      case s if s.isLocalOrFormal =>
        findWhile(
          key,
          s => s.isLocalOrFormal || s.isLambda,
          s =>
            !((s.domain.isLocalOrFormal || s.domain.isLambda) && s.pos >= pos)
        ).orElse(global.find(key))
      case _ => lookup(key)
    }

  /**
    * Declare a symbol in the current scope.
    *
    * @param symbol symbol
    */
  def declare(symbol: Symbol): Unit =
    currentScope.declare(symbol.asInstanceOf[currentScope.Item])
}

object ScopeImplicit {

  implicit class ScopeAnnotatedHasScope[S <: Scope](self: Annotated[S]) {

    /**
      * Access a node that is annotated with a [[Scope]] by the field name `scope`.
      *
      * @example If `x` is annotated with a [[ClassScope]], then {{{ x.scope }}} gives you {{{ x.annot: ClassScope }}}.
      *
      * @return the annotation
      */
    def scope: S = self.annot
  }

}
