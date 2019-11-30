package decaf.printing

import decaf.frontend.annot._
import decaf.lowlevel.log.IndentPrinter

/** Pretty print a scope. Output of PA2. */
class PrettyScope(printer: IndentPrinter)
    extends PrettyPrinter[Scope](printer) {

  override def pretty(scope: Scope): Unit = scope match {
    case s: GlobalScope =>
      printer.println("GLOBAL SCOPE:")
      indent {
        if (s.isEmpty) {
          printer.println("<empty>")
        } else {
          s.values.foreach { symbol =>
            println(symbol.toString)
            printer.println(symbol.toString)
          }
        }
        s.values.foreach { symbol =>
          pretty(symbol.scope)
        }
      }
    case s: ClassScope =>
      printer.println(
        s"CLASS SCOPE OF '${s.owner.name}':"
      )
      indent {
        if (s.isEmpty) {
          printer.println("<empty>")
        } else {
          s.values.foreach { symbol =>
            printer.println(symbol.toString)
          }
        }
        s.values.foreach {
          case m: MethodSymbol => pretty(m.scope)
          case _               => // do not print
        }
      }
    case s: FormalScope =>
      printer.println(s"FORMAL SCOPE OF '${s.owner.name}':")
      indent {
        if (s.isEmpty) {
          printer.println("<empty>")
        } else {
          s.values.foreach { symbol =>
            printer.println(symbol.toString)
          }
        }
        s.owner match {
          case m: MethodSymbol =>
            if (!m.isAbstract)
              pretty(s.nestedScope)
          case l: LambdaSymbol => pretty(s.nestedScope)
          case _ => ;
        }
      }
    case s: LambdaScope =>
      printer.println(s"LOCAL SCOPE:")
      indent {
        if (s.isEmpty) {
          printer.println("<empty>")
        } else {
          s.values.foreach { symbol =>
            printer.println(symbol.toString)
          }
        }
        s.nestedScopes.foreach(pretty)
      }
    case s: LocalScope =>
      printer.println(s"LOCAL SCOPE:")
      indent {
        if (s.isEmpty) {
          printer.println("<empty>")
        } else {
          s.values.foreach{symbol =>
            printer.println(symbol.toString)
          }
        }
        s.nestedScopes.foreach(pretty)
      }
  }
}
