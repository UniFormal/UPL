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
  private val mallocFun = IrDeclFun("malloc", IrFunType(IrPtrType(IrIntType.I64), List(IrIntType.I64)))
  private val declaredFunctions: List[IrDeclFun] = List(mallocFun)

  private val globals: mutable.ArrayBuffer[IrGlobal] = mutable.ArrayBuffer()
  private val structs: mutable.ArrayBuffer[IrStruct] = mutable.ArrayBuffer()
  private val functions: mutable.ArrayBuffer[IrFun] = mutable.ArrayBuffer()
  private val nameCount: mutable.Map[String, Int] = mutable.Map().withDefaultValue(0)
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

      val result = IrVar(thnO.tp, fresh("result"))
      ctx.emit(IrPhi(result, List((thnO, thenB.label), (elsO, elseB.label))))

      result
    case Equality(positive, tp, left, right) => val lO = apply(left)
      val rO = apply(right)
      val cmpResult = IrVar(IrIntType.I1, fresh("cmp_result")) // We only support comparisons of boolean, numbers
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

            val op_result = IrVar(IrIntType.I64, fresh("op_result"))
            ctx.emit(IrBinOp(op_result, irOp, left, right))
            op_result
          }
      }
      case o: OpenRef => applyField(loadOpenRef(o), args)
      case o: ClosedRef => applyField(loadClosedRef(o), args)
      case o: OwnedExpr => applyField(loadOwnedExpr(o), args)
    }
    case o: OpenRef => loadOpenRef(o)
    case r: ClosedRef => loadClosedRef(r)
    case o: OwnedExpr => loadOwnedExpr(o)
    case Lambda(ins, body, _) => val prevCtx = ctx
      ctx = new FunctionContext
      ctx.insertBlock(ctx.newBlock("entry"))

      val result = apply(body)(gc.append(ins))
      ctx.emit(IrReturn(result))

      val params = ins.variables.reverse

      val lambdaFun = IrFun(fresh("lambda"), IrFunType(result.tp, params.map(v => llvmType(v.tp))), params.map(v =>
        IrArgument(llvmType(v.tp), v.name)), ctx.buildBlocks())
      functions += lambdaFun
      ctx = prevCtx
      IrFunctionRef(lambdaFun)
    case VarRef(n) => // TODO This should be reworked
      IrVar(llvmType(gc.lookupLocal(n).get.asInstanceOf[EVarDecl].tp), s"$n")
    case Instance(theory) => val theoryPath = mainTheoryPath(theory)
      val module = gc.lookupGlobal(theoryPath).get.asInstanceOf[Module]
      val exprDecls = module.decls.collect { case d: ExprDecl => d }
      val struct = IrStruct(theoryPath.toString, exprDecls.map { d => llvmType(d.tp) })
      val size = IrVar(IrIntType.I64, fresh("size"))
      ctx.emit(IrComputeSize(size, struct))

      val structPtr = IrVar(IrPtrType(struct), fresh("struct_ptr"))
      ctx.emit(IrCall(Some(structPtr), IrFunctionRef(mallocFun), List(size)))
      val initFun = IrDeclFun(s"${theoryPath}_initialize", IrFunType(IrVoidType, Nil))
      ctx.emit(IrCall(None, IrFunctionRef(initFun), List(structPtr)))

      // Initializes the expression declared by this instance
      theory.decls.foreach { case ExprDecl(name, _, _, Some(exp), _, _) => val fieldIndex = exprDecls.indexWhere(_
        .name == name)
        storeField(struct, structPtr, exp, fieldIndex)
      case _ =>
      }

      structPtr
  }

  def applyField(fieldVar: IrValue, args: List[Expression])(implicit gc: GlobalContext): IrVar = {
    val result = IrVar(fieldVar.tp.asInstanceOf[IrFunType].ret, fresh("result"))

    ctx.emit(IrCall(Some(result), fieldVar, args.map(a => apply(a))))
    result
  }

  def apply(d: Declaration)(implicit gc: GlobalContext): Unit = {
    d match {
      case m@Module(name, closed, df) => val gcI = gc.enter(m)
        val fullName = (gc.currentParent / name).toString
        compileModule(df, closed, fullName, gcI)
    }
  }

  private def fresh(name: String): String = {
    val c = nameCount(name)
    nameCount.update(name, c + 1)
    s"${name}_$c"
  }

  private def storeField(struct: IrStruct, structPtr: IrValue, exp: Expression, fieldIndex: Int)(implicit
    gc: GlobalContext): Unit = {
    val fieldPtr = IrVar(IrPtrType(struct), fresh(s"field_${fieldIndex}_ptr"))
    ctx.emit(IrGetElement(fieldPtr, struct, structPtr, List(0, fieldIndex)))
    ctx.emit(IrStore(apply(exp)(gc), fieldPtr))
  }

  private def loadField(struct: IrStruct, structPtr: IrValue, fieldIndex: Int): IrVar = {
    val fieldPtr = IrVar(IrPtrType(struct.fields(fieldIndex)), fresh(s"field_${fieldIndex}_ptr"))
    ctx.emit(IrGetElement(fieldPtr, struct, structPtr, List(0, fieldIndex)))
    val fieldVar = IrVar(struct.fields(fieldIndex), fresh(s"field_$fieldIndex"))
    ctx.emit(IrLoad(fieldVar, fieldPtr))
    fieldVar
  }

  private def compileModule(df: TheoryValue, closed: Boolean, moduleName: String, gcI: GlobalContext): Unit = { //
    // Recursively traverse other declarations
    // We need to do this before traversing all expression declarations in the current module to prevent inner
    // modules from messing with the function context
    df.decls.foreach { case _: ExprDecl =>
    case _: Include =>
    case d => apply(d)(gcI)
    }

    val exprDecls = df.decls.collect { case d: ExprDecl => d }
    val struct = IrStruct(moduleName, exprDecls.map { d => llvmType(d.tp) })
    structs += struct

    if (closed) { // Function to initialize all struct fields
      ctx = new FunctionContext
      val structArg = IrArgument(IrPtrType(struct), "__instance")
      ctx.insertBlock(ctx.newBlock("entry"))

      df.decls.foreach { case e@ExprDecl(_, _, _, Some(exp), _, _) => val fieldIndex = exprDecls.indexOf(e)
        storeField(struct, structArg, exp, fieldIndex)(gcI)
      case _ =>
      }
      ctx.emit(IrReturnVoid)
      val initializeFun = IrFun(s"${moduleName}_initialize", IrFunType(IrVoidType, Nil), List(structArg), ctx
        .buildBlocks())
      functions += initializeFun

    } else { // The initialized field indicates whether the module has been initialized
      // Fields will be initialized on first module access
      val initializedGlobal = IrGlobal(s"${moduleName}_initialized", IrIntType.I1)
      val structGlobal = IrGlobal(moduleName, struct)
      globals += initializedGlobal
      globals += structGlobal

      // Function to initialize all struct fields
      ctx = new FunctionContext
      ctx.insertBlock(ctx.newBlock("entry"))

      df.decls.foreach { case e@ExprDecl(_, _, _, Some(exp), _, _) => val fieldIndex = exprDecls.indexOf(e)
        storeField(struct, structGlobal, exp, fieldIndex)(gcI)
      case _ =>
      }
      ctx.emit(IrReturnVoid)
      val initializeFun = IrFun(s"${moduleName}_initialize", IrFunType(IrVoidType, Nil), Nil, ctx.buildBlocks())
      functions += initializeFun

      // ensure_initialized is invoked before every field access. It initializes the module if it has not been
      // initialized yet.
      ctx = new FunctionContext
      ctx.insertBlock(ctx.newBlock("entry"))
      val initB = ctx.newBlock("init")
      val endB = ctx.newBlock("end")
      val initialized = IrVar(IrIntType.I1, fresh("initialized"))
      ctx.emit(IrLoad(initialized, initializedGlobal))
      ctx.emit(IrCondBranch(initialized, endB.label, initB.label))
      ctx.insertBlock(initB)
      ctx.emit(IrStore(IrConst(true), initializedGlobal))
      ctx.emit(IrCall(None, IrFunctionRef(initializeFun), Nil))
      ctx.emit(IRBranch(endB.label))

      ctx.insertBlock(endB)
      ctx.emit(IrReturnVoid)
      functions += IrFun(s"${moduleName}_ensure_initialized", IrFunType(IrVoidType, Nil), Nil, ctx.buildBlocks())
    }
  }

  private def loadClosedRef(r: ClosedRef)(implicit gc: GlobalContext): IrValue = {
    val theoryPath = gc.currentParent
    val module = gc.lookupGlobal(theoryPath).get.asInstanceOf[Module]
    val exprDecls = module.decls.collect { case d: ExprDecl => d }
    val fieldIndex = exprDecls.indexWhere(_.name == r.name)
    val struct = IrStruct(theoryPath.toString, exprDecls.map { d => llvmType(d.tp) })

    val instanceArgument = IrArgument(IrPtrType(struct), "__instance")
    loadField(struct, instanceArgument, fieldIndex)
  }

  private def loadOwnedExpr(o: OwnedExpr)(implicit gc: GlobalContext): IrValue = {
    o match {
      case OwnedExpr(owner, ownerDom, ClosedRef(owned)) => val theoryPath = mainTheoryPath(ownerDom)
        val module = gc.lookupGlobal(theoryPath).get.asInstanceOf[Module]
        val exprDecls = module.decls.collect { case d: ExprDecl => d }
        val fieldIndex = exprDecls.indexWhere(e => e.name == owned)
        val struct = IrStruct(theoryPath.toString, exprDecls.map { d => llvmType(d.tp) })

        val structPtr = apply(owner)(gc)
        loadField(struct, structPtr, fieldIndex)
      case _ => ???
    }
  }

  private def loadOpenRef(o: OpenRef)(implicit gc: GlobalContext): IrValue = {
    val field = gc.lookupRef(o).get.asInstanceOf[ExprDecl]
    val path = o.path
    val modulePath = path.up
    val moduleName = if (modulePath.isRoot) {
      TOP_LEVEL_STRUCT_NAME
    } else {
      modulePath.toString
    }
    val initFun = IrDeclFun(s"${moduleName}_ensure_initialized", IrFunType(IrVoidType, Nil))
    ctx.emit(IrCall(None, IrFunctionRef(initFun), Nil))

    val module = gc.lookupGlobal(modulePath).get.asInstanceOf[Module]
    val exprDecls = module.decls.collect { case d: ExprDecl => d }
    val struct = IrStruct(moduleName, exprDecls.map { d => llvmType(d.tp) })
    val fieldIndex = exprDecls.indexOf(field)
    val structGlobal = IrGlobal(moduleName, struct)

    loadField(struct, structGlobal, fieldIndex)
  }

  private def llvmType(tp: Type): IrType = {
    tp match {
      case BoolType => IrIntType.I1
      case _: NumberType => IrIntType.I64
      case FunType(ins, out) => IrFunType(llvmType(out), ins.variables.map(v => llvmType(v.tp)))
      case ClassType(dom) => IrPtrType(IrStruct(mainTheoryPath(dom).toString, Nil))
      case _ => throw new IllegalArgumentException(s"Unsupported type: $tp")
    }
  }

  private def mainTheoryPath(theory: Theory): Path = { // The first include of a theory should always be the 'class
    // type'
    theory.decls.head.asInstanceOf[Include].dom.asInstanceOf[OpenRef].path
  }

  private case class BlockBuilder(label: String, instructions: mutable.ArrayBuffer[IrInstr] = mutable.ArrayBuffer()) {
    def add(i: IrInstr): Unit = instructions += i

    def build() = IrBlock(label, instructions.toList)
  }

  private class FunctionContext {
    private val blocks = mutable.ArrayBuffer[BlockBuilder]()
    var currentBlock: BlockBuilder = _

    def newBlock(name: String): BlockBuilder = {
      BlockBuilder(fresh(name))
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