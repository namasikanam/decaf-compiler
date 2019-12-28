package decaf.frontend.tac

import java.io.PrintWriter

import decaf.driver.{Config, Phase}
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.tree.TypedTree._
import decaf.lowlevel.tac.{ProgramWriter, Simulator, TacProg}
import decaf.util.Conversions._

/**
  * The tacgen phase: translate a typed abstract syntax tree to TAC IR.
  */
class TacGen(implicit config: Config)
    extends Phase[Tree, TacProg]("tacgen", config)
    with TacEmitter {

  /**
    * Transformer entry.
    *
    * @param tree a typed abstract syntax tree
    * @return TAC program
    */
  override def transform(tree: Tree): TacProg = {
    // Create class info.
    val info = tree.classes.map(_.symbol.getInfo)
    val pw = new ProgramWriter(info)

    // Step 1: create virtual tables.
    pw.visitVTables()

    // Step 2: emit tac instructions for every method.
    for {
      clazz <- tree.classes
      method <- clazz.methods
    } yield {
      //   printf(s"Transform (clazz $clazz, method $method)\n")

      if (method.symbol.isMain) {
        val fv = pw.visitMainMethod

        if (!method.isAbstract) {
          emitStmt(method.body)(new Context, Nil, fv)
        }

        fv.visitEnd()
      } else {
        // val base = if (method.isStatic) 0 else 1 // arg 0 is reserved for `this`, when this is a member method
        val base = 1 // The function object is always passed as the first argument
        val fv =
          pw.visitFunc(clazz.name, method.name, base + method.params.length)
        val ctx = new Context
        method.params.zipWithIndex.foreach {
          case (p, i) => ctx.vars(p.symbol) = fv.getArgTemp(base + i)
        }

        if (!method.isAbstract) {
          emitStmt(method.body)(ctx, Nil, fv)
        }

        fv.visitEnd()
      }
    }

    pw.visitEnd()
  }

  /**
    * After generating TAC program, dump it and start the simulator if necessary.
    *
    * @param program TAC program
    */
  override def onSucceed(program: TacProg): Unit = {
    if (config.target.equals(Config.Target.PA3)) { // First dump the tac program to file,
      val path = config.dstDir / config.sourceBaseName + ".tac"
      val printer = new PrintWriter(path)
      program.printTo(printer)
      printer.close()

      // and then execute it using our simulator.
      val simulator = new Simulator(System.in, config.output)
      simulator.execute(program)
    }
  }
}
