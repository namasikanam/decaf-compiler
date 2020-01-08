package decaf.backend.reg

import decaf.backend.asm.{AsmEmitter, Holes, SubroutineEmitter, SubroutineInfo}
import decaf.backend.dataflow._
import decaf.lowlevel.instr.{PseudoInstr, Reg, Temp}
import decaf.lowlevel.Mips

import scala.collection.mutable
import scala.util.Random

/**
  * Brute force greedy register allocation algorithm.
  * To make our life easier, don't consider any special registers that may be used during call.
  */
final class ColoringRegAlloc(emitter: AsmEmitter) extends RegAlloc(emitter) {

  override def apply(graph: CFG[PseudoInstr], info: SubroutineInfo): Unit = {
    // Initialization
    regOf.clear()
    tempOf.clear()
    used.clear()
    neighborOf.clear()

    val subEmitter = emitter.emitSubroutine(info)

    // Build a graph
    // ??????????
    (0 to info.numArgs - 1).foreach(
      i =>
        (0 to info.numArgs - 1).foreach(
          j => addEdge(i, j)
        )
    )
    for (bb <- graph) {
      buildBlock(bb)
    }

    // Calculate the mapping between temps and regs
    alloc()

    // Emit correct MIPS instructions
    (0 to info.numArgs - 1).foreach(
      i => {
        val temp = new Temp(i)
        val reg = if (regOf.contains(temp.index)) regOf(temp.index) else Mips.V1
        subEmitter.emitLoadFromStack(reg, temp)
        bind(reg, temp)
      }
    )
    for (bb <- graph) {
      bb.label.foreach(subEmitter.emitLabel)
      emitBlock(bb, subEmitter)
    }

    subEmitter.emitEnd(used.toSet)
  }

  /**
    *
    * @param bb  the basic block to build a graph from
    */
  private def buildBlock(
      bb: BasicBlock[PseudoInstr]
  ): Unit = {
    bb.iterator.foreach {
      case loc if loc.instr.isInstanceOf[Holes.CallerSave.type]    => None
      case loc if loc.instr.isInstanceOf[Holes.CallerRestore.type] => None
      case loc                                                     =>
        // Dst - liveout
        loc.instr.dsts.foreach(dst => {
          loc.liveOut.foreach(liveTmp => {
            addEdge(dst.index, liveTmp.index)
          })
        })
        // livein - livein
        loc.liveIn.foreach(
          liveTmp1 => {
            loc.liveIn.foreach(
              liveTmp2 => addEdge(liveTmp1.index, liveTmp2.index)
            )
          }
        )
    }
  }

  /**
    * ???20?????????????[[emitter.allocatableRegs]]?
    * use greedy strategy to allocate regs and temps
    */
  private def alloc(): Unit = {
    if (!neighborOf.isEmpty) {
      // Find a node whose degree is less than 20
      neighborOf
        .find(_._2.size < 19)
        .map(
          x => {
            // Remove the node from the graph
            val node = x._1
            val neighbors = neighborOf(node)
            neighborOf.remove(node)
            neighborOf.foreach(_._2 -= node)
            // Recursive allocation
            alloc()
            // Get a reg for current node
            // based on the calculated information
            var restRegs = emitter.allocatableRegs.toSet
            neighbors.foreach(restRegs -= regOf(_))
            regOf += (node -> restRegs.find(_ => true).get)
          }
        )
    }
  }

  /**
    * @param bb the basic block to emit MIPS instructions
    */
  private def emitBlock(
      bb: BasicBlock[PseudoInstr],
      subEmitter: SubroutineEmitter
  ): Unit = {
    val callerNeedSave = new mutable.ArrayBuffer[Reg]

    bb.iterator.foreach {
      case loc if loc.instr.isInstanceOf[Holes.CallerSave.type] =>
        for (reg <- emitter.callerSaveRegs) {
          if (tempOf.contains(reg) && loc.liveOut
                .find(_.index == tempOf(reg).index)
                .isDefined) {
            // printf(s"callerNeedSave += $reg\n")

            callerNeedSave += reg
            subEmitter.emitStoreToStack(reg, tempOf(reg))
          }
        }
      case loc if loc.instr.isInstanceOf[Holes.CallerRestore.type] =>
        callerNeedSave.foreach { reg =>
          subEmitter.emitLoadFromStack(reg, tempOf(reg))
        }
      case loc =>
        val instr = loc.instr
        val srcRegs = new Array[Reg](instr.srcs.length)
        val dstRegs = new Array[Reg](instr.dsts.length)

        for (i <- instr.srcs.indices) {
          instr.srcs(i) match {
            case reg: Reg => srcRegs(i) = reg
            case temp =>
              val reg =
                if (regOf.contains(temp.index)) regOf(temp.index) else Mips.V1
              srcRegs(i) = reg
              bind(reg, temp)
          }
        }

        for (i <- instr.dsts.indices) {
          instr.dsts(i) match {
            case reg: Reg => dstRegs(i) = reg
            case temp =>
              val reg =
                if (regOf.contains(temp.index)) regOf(temp.index) else Mips.V1
              dstRegs(i) = reg
              bind(reg, temp)
          }
        }

        subEmitter.emitNative(instr.toNative(dstRegs, srcRegs))
    }
  }

  /** Bind a temp with a register. */
  private def bind(reg: Reg, temp: Temp): Unit = {
    used += reg
    tempOf(reg) = temp
  }

  // Color
  val regOf = new mutable.TreeMap[Int, Reg]

  // Runtime information
  val tempOf = new mutable.TreeMap[Reg, Temp]

  val used = new mutable.TreeSet[Reg]

  // Graph
  val neighborOf = new mutable.TreeMap[Int, mutable.TreeSet[Int]]
  private def addEdge(x: Int, y: Int): Unit = {
    if (x != y) {
      addDirectedEdge(x, y)
      addDirectedEdge(y, x)
    }
  }
  private def addDirectedEdge(x: Int, y: Int): Unit = {
    if (!neighborOf.contains(x)) neighborOf += (x -> new mutable.TreeSet[Int])
    neighborOf(x) += y
  }
}
