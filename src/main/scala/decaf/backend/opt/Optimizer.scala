package decaf.backend.opt

import java.io.PrintWriter

import decaf.driver.{Config, Phase}
import decaf.lowlevel.tac.{Simulator, TacProg, TacFunc, TacInstr}
import decaf.lowlevel.instr.PseudoInstr
import decaf.printing.PrettyCFG
import decaf.backend.dataflow.{CFG, LivenessAnalyzer}

import collection.JavaConverters._

/**
  * TAC optimization phase: optimize a TAC program.
  *
  */
class Optimizer(implicit config: Config)
    extends Phase[TacProg, TacProg]("optimizer", config) {

  /**
    * Transformer entry.
    *
    * @param func a TAC program
    * @return also a TAC program, but optimized
    */
  override def transform(tacProg: TacProg): TacProg = {
    // 调用CFG
    val analyzer = new LivenessAnalyzer[TacInstr]

    var funcs = tacProg.funcs.asScala
    var changed = false
    do {
      changed = false

      funcs.foreach(func => {
        val instrSeq = func.getInstrSeq().asScala
        val cfg = CFG.buildFrom(instrSeq.toList)
        analyzer(cfg)

        // 进入CFG分析
        val block_it = cfg.iterator
        while (block_it.hasNext) {
          val loc_it = block_it.next().seqIterator
          while (loc_it.hasNext) {
            val loc = loc_it.next()
            val instr = loc.instr

            // 是否产生了赋值
            if (!instr.dsts.isEmpty) {
              // 被赋值的 Temp 是否是活跃变量
              if (!loc.liveOut.contains(instr.dsts(0))) {
                // printf(s"${instr.dsts(0)} is not live!\n")

                // 是否是一个 call 赋值给 Temp
                if (!instr.isInstanceOf[TacInstr.IndirectCall] && !instr
                      .isInstanceOf[TacInstr.DirectCall]) {
                  instrSeq -= instr

                  changed = true
                }
              }
            }
          }
        }
      })
    } while (changed)

    tacProg
  }

  /**
    *
    * @param instrIndex
    * @return
    */
  def optimizeInstr(
      instrIndex: Int
  )(implicit inputSeq: List[TacInstr], outputFunc: TacFunc): Unit = {}

  /**
    * After generating the optimized TAC program, dump it and start the simulator if necessary.
    *
    * @param program Tac program
    */
  override def onSucceed(program: TacProg): Unit = {
    if (config.target.equals(Config.Target.PA4)) { // First dump the tac program to file,
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
