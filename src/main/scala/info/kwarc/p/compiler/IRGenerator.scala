package info.kwarc.p.compiler

import info.kwarc.p.compiler.Condition.{EQUAL, NOT_EQUAL}
import info.kwarc.p.{ApproxReal, BaseValue, BoolValue, Declaration, Equality, Expression, GlobalContext, IfThenElse, NumberValue, Program, Rat, StringValue, UnitValue}

import scala.collection.mutable

object IRGenerator {
  def run(p: Program): IRProgram = {
    val voc = p.voc
    val ig = new IRGenerator()

    val gc = GlobalContext(voc)
    voc.decls.foreach(d => ig.apply(d)(gc))

    ig.compileMain(p.main)(gc)

    IRProgram(
      ig.structs.toList,
      ig.declaredFunctions,
      ig.functions.toList
    )
  }
}

private class IRGenerator {
  private val mallocFun =
    IRDeclFun("malloc", IrPtrType(IrIntType.I64), List(IrIntType.I64))
  private val declaredFunctions: List[IRDeclFun] = List(mallocFun)

  private val structs: mutable.ArrayBuffer[IRStruct] = mutable.ArrayBuffer()
  private val functions: mutable.ArrayBuffer[IRFun] = mutable.ArrayBuffer()

  private var ctx: FunctionContext = _

  def compileMain(exp: Expression)(implicit gc: GlobalContext): Unit = {
    ctx = new FunctionContext

    val entry = ctx.newBlock("entry")
    ctx.insertBlock(entry)
    val value = apply(exp)(gc)
    ctx.emit(IrReturn(value))

    // We currently assume that the main expression evaluates to a 64-bit integer.
    val mainFun = IRFun(
      "main",
      IrIntType.I64,
      Nil,
      ctx.buildBlocks()
    )
    functions += mainFun
  }

  def apply(
      exp: Expression
  )(implicit gc: GlobalContext): IrOperand = exp match {
    // TODO Currently all numbers are treated as i64 integers.
    case NumberValue(_, re, _) =>
      re match {
        case ApproxReal(value) => IrConst(value.toInt)
        case Rat(enu, deno)    => IrConst(enu.toInt / deno.toInt)
      }
    // Booleans are represented using i1 integers.
    case BoolValue(value) => IrConst(value)
    // Unit value is represented as a special constant to make it easy to spot when debugging
    case UnitValue                        => IrConst(0xdeadbeef)
    case IfThenElse(cond, thn, Some(els)) =>
      // Based on ideas from
      // https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl05.html#if-then-else
      var thenB = ctx.newBlock("then")
      var elseB = ctx.newBlock("else")
      val endB = ctx.newBlock("end")

      // This needs to evaluate to a 1-bit integer.
      val condO = apply(cond)
      assert(condO.tp == IrIntType.I1)
      ctx.emit(IrCondBranch(condO, thenB.label, elseB.label))

      ctx.insertBlock(thenB)
      val thnO = apply(thn)
      ctx.emit(IRBranch(endB.label))
      thenB = ctx.currentBlock

      ctx.insertBlock(elseB)
      val elsO = apply(els)
      ctx.emit(IRBranch(endB.label))
      elseB = ctx.currentBlock

      ctx.insertBlock(endB)

      val result = IrVar(thnO.tp, ctx.fresh("result"))
      ctx.emit(IrPhi(result, List((thnO, thenB.label), (elsO, elseB.label))))

      result
    case Equality(positive, tp, left, right) =>
      val lO = apply(left)
      val rO = apply(right)
      val cmpResult = IrVar(IrIntType.I1, ctx.fresh("cmp_result"))
      // We only support comparisons of boolean, numbers (approximated as i64) and UnitValue
      assert(left.isInstanceOf[BaseValue])
      assert(right.isInstanceOf[BaseValue])
      assert(!left.isInstanceOf[StringValue])
      assert(!right.isInstanceOf[StringValue])

      ctx.emit(IrICmp(cmpResult, if (positive) EQUAL else NOT_EQUAL, lO, rO))
      cmpResult
  }

  def apply(
      d: Declaration
  )(implicit gc: GlobalContext): Unit = {}

  private case class BlockBuilder(
      label: String,
      instructions: mutable.ArrayBuffer[IrInstr] = mutable.ArrayBuffer()
  ) {
    def add(i: IrInstr): Unit = instructions += i

    def build() = IrBlock(label, instructions.toList)
  }

  private class FunctionContext {
    private val blocks = mutable.ArrayBuffer[BlockBuilder]()
    private val nameCount: mutable.Map[String, Int] =
      mutable.Map().withDefaultValue(0)
    var currentBlock: BlockBuilder = _

    def newBlock(name: String): BlockBuilder = {
      BlockBuilder(fresh(name))
    }

    def fresh(name: String): String = {
      val c = nameCount(name)
      nameCount.update(name, c + 1)
      s"${name}_$c"
    }

    def insertBlock(b: BlockBuilder): Unit = {
      blocks += b
      currentBlock = b
    }

    def emit(instr: IrInstr): Unit = {
      currentBlock.add(instr)
    }

    def buildBlocks(): List[IrBlock] =
      blocks.map(_.build()).toList

  }
}
