package info.kwarc.p.compiler

import info.kwarc.p._
import info.kwarc.p.compiler.Condition.{EQUAL, NOT_EQUAL, SIGNED_GREATER_EQUAL, SIGNED_GREATER_THAN, SIGNED_LESS_EQUAL, SIGNED_LESS_THAN}
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

case class Variable(name: String, irValue: IrVar)
case class VariableScope(var variables: List[Variable] = List())

private class IRGenerator {
  private val mallocFun = IrDeclFun("malloc", IrFunType(IrPtrType(IrIntType.I64), List(IrIntType.I64)))
  private val declaredFunctions: mutable.ArrayBuffer[IrDeclFun] = mutable.ArrayBuffer(mallocFun)

  private val globals: mutable.ArrayBuffer[IrGlobal] = mutable.ArrayBuffer()
  private val structs: mutable.ArrayBuffer[IrStruct] = mutable.ArrayBuffer()
  private val functions: mutable.ArrayBuffer[IrFun] = mutable.ArrayBuffer()
  private val nameCount: mutable.Map[String, Int] = mutable.Map().withDefaultValue(0)
  private var scopes: List[VariableScope] = List(VariableScope(List()))
  private var ctx: FunctionContext = _

  private def getAllocatedVariable(n: String): IrVar = scopes.find(_.variables.exists(_.name == n)).map(_.variables.find(_.name == n).get).getOrElse(throw new RuntimeException(s"Variable $n not found")).irValue

  def compileMain(exp: Expression)(implicit gc: GlobalContext): Unit = {
    ctx = new FunctionContext

    val entry = ctx.newBlock("entry")
    ctx.insertBlock(entry)
    val value = apply(exp)(gc)
    //not every code statement returns a value => behave like C; default to 0
    val ret = value.tp match {
      case IrVoidType => IrReturn(IrConst(IrIntType.I64, 0))
      case _ => IrReturn(value)
    }
    ctx.emit(ret)

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
    case StringValue(value) =>
      val v = IrGlobal(fresh("name"), IrConstChar(value.length), Some(s"c\"$value\\00\""))
      globals.append(v)
      v
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
      val allocResult = IrVar(IrPtrType(thnO.tp), fresh("alloc_result"))
      ctx.emit(IrStore(thnO, allocResult))
      ctx.emit(IRBranch(endB.label))
      thenB = ctx.currentBlock

      ctx.insertBlock(elseB)
      val elsO = apply(els)
      ctx.emit(IrStore(elsO, allocResult))
      ctx.emit(IRBranch(endB.label))
      elseB = ctx.currentBlock

      ctx.insertBlock(endB)

      ctx.emitFirst(IrAlloca(allocResult))

      val result = IrVar(thnO.tp, fresh("result"))
      ctx.emit(IrLoad(result, allocResult))

      result
    case IfThenElse(cond, thn, _) =>
      var thenB = ctx.newBlock("then")
      val endB = ctx.newBlock("end")

      ctx.emit(IrCondBranch(apply(cond), thenB.label, endB.label))

      ctx.insertBlock(thenB)
      val thnO = apply(thn)
      val allocResult = IrVar(IrPtrType(thnO.tp), fresh("alloc_result"))
      ctx.emit(IrStore(thnO, allocResult))
      ctx.emit(IRBranch(endB.label))
      thenB = ctx.currentBlock

      ctx.insertBlock(endB)

      ctx.emitFirst(IrAlloca(allocResult))

      val result = IrVar(thnO.tp, fresh("result"))
      ctx.emit(IrLoad(result, allocResult))

      result
    case While(cond, body) =>
      val bodyB = ctx.newBlock("body")
      val loopB = ctx.newBlock("loop")
      val endB = ctx.newBlock("end")

      ctx.emit(IRBranch(loopB.label))
      ctx.insertBlock(bodyB)
      apply(body)
      ctx.emit(IRBranch(loopB.label))
      ctx.insertBlock(loopB)
      ctx.emit(IrCondBranch(apply(cond), bodyB.label, endB.label))
      ctx.insertBlock(endB)

      apply(Unit.Value)
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
        case inf: Comparison =>
          val irCond = inf match {
            case Greater => SIGNED_GREATER_THAN
            case GreaterEq => SIGNED_GREATER_EQUAL
            case Less => SIGNED_LESS_THAN
            case LessEq => SIGNED_LESS_EQUAL
            case _ => ???
          }
          val cmpResult = IrVar(IrIntType.I1, fresh("cmp_result"))
          ctx.emit(IrICmp(cmpResult, irCond, apply(args(0)), apply(args(1))))
          cmpResult
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
      val params = ins.variables.reverse
      val arguments = params.map(v => IrArgument(llvmType(v.tp), v.name))

      scopes ::= VariableScope(Nil)
      arguments.foreach { a =>
        val allocatedVar = IrVar(IrPtrType(a.tp), fresh(s"alloc_arg_${a.name}"))
        ctx.emitFirst(IrAlloca(allocatedVar))

        scopes.head.variables ::= Variable(a.name, allocatedVar)
        ctx.emit(IrStore(a, allocatedVar))
      }

      val result = apply(body)(gc.append(ins))
      scopes = scopes.tail

      ctx.emit(IrReturn(result))

      val lambdaFun = IrFun(fresh("lambda"), IrFunType(result.tp, params.map(v => llvmType(v.tp))), arguments, ctx.buildBlocks())
      functions += lambdaFun
      ctx = prevCtx
      IrFunctionRef(lambdaFun)
    case Block(exprs) =>
      scopes ::= VariableScope(Nil)
      val result = if (exprs.nonEmpty) {
        exprs.dropRight(1).foreach { e => apply(e) }
        apply(exprs.last)
      } else {
        // dummy value (Unit.Value)
        apply(Unit.Value)
      }
      scopes = scopes.tail
      result
    case VarRef(n) =>
      val allocatedVariable = getAllocatedVariable(n)
      allocatedVariable.tp match {
        case tp: IrPtrType => val result = IrVar(tp.to, fresh(n))
          ctx.emit(IrLoad(result, allocatedVariable))
          result
        case _ => ???
      }
    case Return(exp, false) =>
      val value = apply(exp)
      ctx.emit(value.tp match {
        case IrVoidType => IrReturnVoid
        case _ => IrReturn(value)
      })
      apply(Unit.Value)
    case EVarDecl(name, tp, Some(e), _, _) =>
      val res = apply(e)
      val allocatedVar = IrVar(IrPtrType(llvmType(tp)), fresh(s"alloc_$name"))
      ctx.emitFirst(IrAlloca(allocatedVar))

      scopes.head.variables ::= Variable(name, allocatedVar)
      ctx.emit(IrStore(res, allocatedVar))
      allocatedVar
    case Assign(VarRef(n), value) =>
      val allocatedVariable = getAllocatedVariable(n)
      ctx.emit(IrStore(apply(value), allocatedVariable))
      apply(Unit.Value)
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

  private def applyField(fieldVar: IrValue, args: List[Expression])(implicit gc: GlobalContext): IrVar = {
    val result = IrVar(fieldVar.tp.asInstanceOf[IrFunType].ret, fresh("result"))

    val option = result.tp match {
      case IrVoidType => None
      case _ => Some(result)
    }

    ctx.emit(IrCall(option, fieldVar, args.map(a => apply(a))))
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
    //special case: generate IR for builtins
    if (module.name == "Uniformal"){
      val builtin = loadBuiltin(path.names(1))
      //builtin.signature
      return IrFunctionRef(builtin)
    }

    loadField(struct, structGlobal, fieldIndex)
  }

  private def loadBuiltin(name: String): IrFun = {
    val definition = builtins.Builtins.find(x => x.name == name)
      .getOrElse(throw new NotImplementedError(s"builtin $name doesn't have a signature"))

    var function: IrFun = null
    //declare llvm builtin
    if(!functions.exists(x => x.name == s"Builtin.$name")) {
      val decl = IrDeclFun(definition.llvmBuiltin, IrFunType(definition.retType, definition.param))
      declaredFunctions.append(decl)
      var i = 0
      val params = definition.param.map(x => {

        val arg = IrArgument(x, s"param$i")
        i = i +1
        arg
      })

      val ret = IrVar(definition.retType, "res")
      val call = IrCall(Some(ret), new IrFunctionRef(decl), params)

      function = IrFun(s"Builtin.$name", IrFunType(definition.retType, definition.param), params,
        List(IrBlock("builtin", List(call, IrReturn(ret)))))
      //add function itself
      functions.append(function)

      return function
    }else{
      functions.find(x => x.name == s"Builtin.$name").getOrElse(throw new NotImplementedError())
    }
  }

  private def llvmType(tp: Type): IrType = {
    tp match {
      case BoolType => IrIntType.I1
      case _: NumberType => IrIntType.I64
      case FunType(ins, out) => IrFunType(llvmType(out), ins.variables.map(v => llvmType(v.tp)))
      case ClassType(dom) => IrPtrType(IrStruct(mainTheoryPath(dom).toString, Nil))
      case EmptyType => IrVoidType
      case u: UnknownType if u.known => llvmType(u.skipUnknown)
      case StringType => IrPtrType(IrConstChar(0))
      case _ => throw new IllegalArgumentException(s"Unsupported type: $tp")
    }
  }

  private def mainTheoryPath(theory: Theory): Path = { // The first include of a theory should always be the 'class
    // type'
    theory.decls.head.asInstanceOf[Include].dom.asInstanceOf[OpenRef].path
  }

  private case class BlockBuilder(label: String, instructions: mutable.ArrayBuffer[IrInstr] = mutable.ArrayBuffer()) {
    def addFirst(i: IrInstr): Unit = instructions.prepend(i)

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

    def emitFirst(instr: IrInstr): Unit = {
      blocks(0).addFirst(instr)
    }

    def emit(instr: IrInstr): Unit = {
      currentBlock.add(instr)
    }

    def buildBlocks(): List[IrBlock] = blocks.map(_.build()).toList
  }
}