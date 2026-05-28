package info.kwarc.p.compiler

import info.kwarc.p.compiler.Condition.{EQUAL, NOT_EQUAL}
import info.kwarc.p.compiler.Operation.{IADD, IDIV, IMUL, ISUB}
import info.kwarc.p._

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

  /** Compiles an expression
    * All instructions will be inserted into the current block / function context.
    * @param exp Expression to compile
    * @return IrOperand representing the result of the expression.
    */
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
      assert(lO.tp.isInstanceOf[IrIntType])
      assert(rO.tp.isInstanceOf[IrIntType])

      ctx.emit(IrICmp(cmpResult, if (positive) EQUAL else NOT_EQUAL, lO, rO))
      cmpResult
    case Application(bo @ BaseOperator(operator, tp), args) =>
      operator match {
        case inf: InfixOperator =>
          val numArgs = args.length
          if (numArgs == 0) {
            apply(inf.neutral.get)
          } else if (numArgs == 1) {
            apply(args(0))
          } else {
            val irOp = inf match {
              case Plus   => IADD
              case Minus  => ISUB
              case Times  => IMUL
              case Divide => IDIV
              case _      => ???
            }

            val (left, right) =
              if (numArgs > 2) {
                if (inf.assoc == RightAssociative) {
                  (apply(args(0)), apply(Application(bo, args.tail)))
                } else {
                  (apply(Application(bo, args.init)), apply(args.last))
                }
              } else {
                (apply(args(0)), apply(args(1)))
              }

            val op_result = IrVar(IrIntType.I64, ctx.fresh("op_result"))
            ctx.emit(IrBinOp(op_result, irOp, left, right))
            op_result
          }
      }

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
