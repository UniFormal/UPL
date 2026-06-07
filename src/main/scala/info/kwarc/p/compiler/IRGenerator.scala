package info.kwarc.p.compiler

import info.kwarc.p._
import info.kwarc.p.compiler.Condition.{EQUAL, NOT_EQUAL}
import info.kwarc.p.compiler.IRGenerator.TOP_LEVEL_STRUCT_NAME
import info.kwarc.p.compiler.Operation.{IADD, IDIV, IMUL, ISUB}

import scala.collection.mutable

object IRGenerator {
  val TOP_LEVEL_STRUCT_NAME = "__top_level"

  def run(p: Program): IrProgram = {
    val ig = new IRGenerator()

    val gc = GlobalContext(p.voc)
    ig.compileModule(p.voc, closed = false, TOP_LEVEL_STRUCT_NAME, gc)
    ig.compileMain(p.main)(gc)

    IrProgram(ig.declaredFunctions, ig.structs.toList, ig.globals.toList, ig.functions.toList)
  }
}

private class IRGenerator {
  private val mallocFun = IrDeclFun("malloc", IrPtrType(IrIntType.I64), List(IrIntType.I64))
  private val declaredFunctions: List[IrDeclFun] = List(mallocFun)

  private val globals: mutable.ArrayBuffer[IrGlobal] = mutable.ArrayBuffer()
  private val structs: mutable.ArrayBuffer[IrStruct] = mutable.ArrayBuffer()
  private val functions: mutable.ArrayBuffer[IrFun] = mutable.ArrayBuffer()

  private var ctx: FunctionContext = _

  def compileMain(exp: Expression)(implicit gc: GlobalContext): Unit = {
    ctx = new FunctionContext

    val entry = ctx.newBlock("entry")
    ctx.insertBlock(entry)
    val value = apply(exp)(gc)
    ctx.emit(IrReturn(value))

    // We currently assume that the main expression evaluates to a 64-bit integer.
    val mainFun = IrFun("main", IrFunType(IrIntType.I64, Nil), Nil, ctx.buildBlocks())
    functions += mainFun
  }

  private def compileModule(df: TheoryValue, closed: Boolean, moduleName: String, gcI: GlobalContext): Unit = {
    val fields = df.decls.collect { case d: ExprDecl => llvmType(d.tp) }

    val struct = IrStruct(moduleName, fields)
    structs += struct

    if (closed) {
      ???
    } else { // The initialized field indicates whether the module has been initialized
      // Fields will be initialized on first module access
      val initializedGlobal = IrGlobal(s"${moduleName}_initialized", IrIntType.I1)
      val structGlobal = IrGlobal(moduleName, struct)
      globals += initializedGlobal
      globals += structGlobal

      // Function to initialize all struct fields
      ctx = new FunctionContext
      ctx.insertBlock(ctx.newBlock("entry"))

      df.decls.foreach { case e@ExprDecl(name, _, _, Some(exp), _, _) => val result = apply(exp)(gcI)
        val fieldIndex = df.decls.collect { case d: ExprDecl => d }.indexOf(e)
        val fieldPtr = IrVar(IrPtrType(struct), ctx.fresh(s"$moduleName.${name}_ptr"))
        ctx.emit(IrGetElement(fieldPtr, struct, structGlobal, List(0, fieldIndex)))
        ctx.emit(IrStore(result, fieldPtr))
      case _ =>
      }
      ctx.emit(IrReturnVoid)
      val initializeFun = IrFun(s"${moduleName}_initialize", IrFunType(IrVoidType, Nil), Nil, ctx.buildBlocks())
      functions += initializeFun

      ctx = new FunctionContext
      ctx.insertBlock(ctx.newBlock("entry"))
      val initB = ctx.newBlock("init")
      val endB = ctx.newBlock("end")
      val initialized = IrVar(IrIntType.I1, ctx.fresh("initialized"))
      ctx.emit(IrLoad(initialized, initializedGlobal))
      ctx.emit(IrCondBranch(initialized, endB.label, initB.label))
      ctx.insertBlock(initB)
      ctx.emit(IrCall(None, IrFunctionRef(initializeFun), Nil))
      ctx.emit(IrStore(IrConst(true), initializedGlobal))
      ctx.emit(IRBranch(endB.label))

      ctx.insertBlock(endB)
      ctx.emit(IrReturnVoid)
      functions += IrFun(s"${moduleName}_ensure_initialized", IrFunType(IrVoidType, Nil), Nil, ctx.buildBlocks())

      // Recursively traverse other declarations
      // We need to do this after traversing all expression declarations in the current module to prevent inner
      // modules from messing with the function context
      df.decls.foreach { case _: ExprDecl =>
      case d => apply(d)(gcI)
      }
    }
  }

  /** Compiles an expression
   * All instructions will be inserted into the current block / function context.
   *
   * @param exp Expression to compile
   * @return IrOperand representing the result of the expression. */
  def apply(exp: Expression)(implicit gc: GlobalContext): IrValue = exp match { // TODO Currently all numbers are
    // treated as i64 integers.
    case NumberValue(_, re, _) => re match {
      case ApproxReal(value) => IrConst(value.toInt)
      case Rat(enu, deno) => IrConst(enu.toInt / deno.toInt)
    } // Booleans are represented using i1 integers.
    case BoolValue(value) => IrConst(value) // Unit value is represented as a special constant to make it easy to
    // spot when debugging
    case Unit.Value => IrConst(0xdeadbeef) // note that Unit.Value is defined
    case IfThenElse(cond, thn, Some(els)) => // Based on ideas from
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
    case Equality(positive, tp, left, right) => val lO = apply(left)
      val rO = apply(right)
      val cmpResult = IrVar(IrIntType.I1, ctx.fresh("cmp_result")) // We only support comparisons of boolean, numbers
      // (approximated as i64) and UnitValue
      assert(lO.tp.isInstanceOf[IrIntType])
      assert(rO.tp.isInstanceOf[IrIntType])

      ctx.emit(IrICmp(cmpResult, if (positive) EQUAL else NOT_EQUAL, lO, rO))
      cmpResult
    case Application(f, args) => f match {
      case bo@BaseOperator(operator, tp) => operator match {
        case inf: InfixOperator => val numArgs = args.length
          if (numArgs == 0) {
            apply(inf.neutral.get)
          } else if (numArgs == 1) {
            apply(args(0))
          } else {
            val irOp = inf match {
              case Plus => IADD
              case Minus => ISUB
              case Times => IMUL
              case Divide => IDIV
              case _ => ???
            }

            val (left, right) = if (numArgs > 2) {
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
      case o: OpenRef => val fieldVar = loadOpenRef(gc, o)
        val result = IrVar(fieldVar.tp.asInstanceOf[IrFunType].ret, ctx.fresh("result"))

        ctx.emit(IrCall(Some(result), fieldVar, args.map(a => apply(a))))
        result
    }
    case o: OpenRef => loadOpenRef(gc, o)
    case Lambda(ins, body, _) => val prevCtx = ctx
      ctx = new FunctionContext
      ctx.insertBlock(ctx.newBlock("entry"))

      val result = apply(body)(gc.append(ins))
      ctx.emit(IrReturn(result))

      val params = ins.variables.reverse

      val lambdaFun = IrFun(ctx.fresh("lambda"), IrFunType(result.tp, params.map(v => llvmType(v.tp))), params.map(v
      => IrArgument(llvmType(v.tp), v.name)), ctx.buildBlocks())
      functions += lambdaFun
      ctx = prevCtx
      IrFunctionRef(lambdaFun)
    case VarRef(n) => IrVar(llvmType(gc.lookupLocal(n).get.asInstanceOf[EVarDecl].tp), s"$n")
  }

  def apply(d: Declaration)(implicit gc: GlobalContext): Unit = {
    d match {
      case m@Module(name, closed, df) => val gcI = gc.enter(m)
        val fullName = (gc.currentParent / name).toString
        compileModule(df, closed, fullName, gcI)
    }
  }

  private def loadOpenRef(gc: GlobalContext, o: OpenRef): IrValue = {
    val field = gc.lookupRef(o).get.asInstanceOf[ExprDecl]
    val path = o.path
    val modulePath = path.up
    val moduleName = if (modulePath.isRoot) {
      TOP_LEVEL_STRUCT_NAME
    } else {
      modulePath.toString
    }
    val module = gc.lookupGlobal(modulePath).get.asInstanceOf[Module]
    val fieldIndex = module.decls.collect { case d: ExprDecl => d }.indexOf(field)
    val struct = structs.find(_.name == moduleName).get
    val structGlobal = globals.find(_.name == moduleName).get
    val initFun = functions.find(_.name == s"${moduleName}_ensure_initialized").get

    val fieldPtr = IrVar(IrPtrType(struct.fields(fieldIndex)), ctx.fresh(s"${path}_ptr"))
    ctx.emit(IrCall(None, IrFunctionRef(initFun), Nil))
    ctx.emit(IrGetElement(fieldPtr, struct, structGlobal, List(0, fieldIndex)))
    val fieldVar = IrVar(struct.fields(fieldIndex), ctx.fresh(s"$path"))
    ctx.emit(IrLoad(fieldVar, fieldPtr))
    fieldVar
  }

  private def llvmType(tp: Type): IrType = {
    tp match {
      case BoolType => IrIntType.I1
      case _: NumberType => IrIntType.I64
      case FunType(ins, out) => IrFunType(llvmType(out), ins.variables.map(v => llvmType(v.tp)))
      case _ => throw new IllegalArgumentException(s"Unsupported type: $tp")
    }
  }

  private case class BlockBuilder(label: String, instructions: mutable.ArrayBuffer[IrInstr] = mutable.ArrayBuffer()) {
    def add(i: IrInstr): Unit = instructions += i

    def build() = IrBlock(label, instructions.toList)
  }

  private class FunctionContext {
    private val blocks = mutable.ArrayBuffer[BlockBuilder]()
    private val nameCount: mutable.Map[String, Int] = mutable.Map().withDefaultValue(0)
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

    def buildBlocks(): List[IrBlock] = blocks.map(_.build()).toList
  }
}