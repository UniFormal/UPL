package info.kwarc.p.compiler

import info.kwarc.p._
import info.kwarc.p.compiler.Condition.{EQUAL, NOT_EQUAL, SIGNED_GREATER_EQUAL, SIGNED_GREATER_THAN, SIGNED_LESS_EQUAL, SIGNED_LESS_THAN}
import info.kwarc.p.compiler.IRGenerator.TOP_LEVEL_STRUCT_NAME
import info.kwarc.p.compiler.Operation.{IADD, IAND, IDIV, IMUL, ISUB}

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
case class VariableScope(var variables: List[Variable] = Nil)

object SpecialFunctions {
  val mallocFun = IrDeclFun("malloc", IrFunType(IrPtrType(IrIntType.I64), List(IrIntType.I64)))

  val stdin = IrGlobalExtern("stdin", IrPtrType(null))
}


private class IRGenerator {

  private val declaredFunctions: mutable.ArrayBuffer[IrDeclFun] = mutable.ArrayBuffer(SpecialFunctions.mallocFun)

  private val globals: mutable.ArrayBuffer[IrGlobalValue] = mutable.ArrayBuffer(SpecialFunctions.stdin)
  private val structs: mutable.ArrayBuffer[IrStruct] = mutable.ArrayBuffer()
  private val functions: mutable.ArrayBuffer[IrFun] = mutable.ArrayBuffer()

  private val nameCount: mutable.Map[String, Int] = mutable.Map().withDefaultValue(0)
  private val prodStructName: mutable.Map[List[IrType], String] = mutable.Map()
  private var scopes: List[VariableScope] = List(VariableScope(List()))

  private var ctx: FunctionContext = _

  private def getAllocatedVariable(n: String): IrVar = scopes.find(_.variables.exists(_.name == n)).map(_.variables.find(_.name == n).get).getOrElse(throw new RuntimeException(s"Variable $n not found")).irValue

  def compileMain(exp: Expression)(implicit gc: GlobalContext): Unit = {
    ctx = new FunctionContext

    val entry = ctx.newBlock("entry")
    ctx.insertBlock(entry)
    val value = compileExpression(exp)(gc)
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
  private def compileExpression(exp: Expression)(implicit gc: GlobalContext): IrValue = exp match { // TODO Currently all numbers are
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

      val condO = compileDynamicBoolean(cond)
      ctx.emit(IrCondBranch(condO, thenB.label, elseB.label))

      ctx.insertBlock(thenB)
      val thnO = compileExpression(thn)
      val allocResult = IrVar(IrPtrType(thnO.tp), fresh("alloc_result"))
      ctx.emit(IrStore(thnO, allocResult))
      ctx.emit(IRBranch(endB.label))
      thenB = ctx.currentBlock

      ctx.insertBlock(elseB)
      val elsO = compileExpression(els)
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

      ctx.emit(IrCondBranch(compileDynamicBoolean(cond), thenB.label, endB.label))

      ctx.insertBlock(thenB)
      val thnO = compileExpression(thn)
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
      compileExpression(body)
      ctx.emit(IRBranch(loopB.label))
      ctx.insertBlock(loopB)
      ctx.emit(IrCondBranch(compileExpression(cond), bodyB.label, endB.label))
      ctx.insertBlock(endB)

      compileExpression(Unit.Value)
    case Equality(positive, tp, left, right) => val lO = compileExpression(left)
      val rO = compileExpression(right)
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
          ctx.emit(IrICmp(cmpResult, irCond, compileExpression(args(0)), compileExpression(args(1))))
          cmpResult
        case inf: InfixOperator => val numArgs = args.length
          if (numArgs == 0) {
            compileExpression(inf.neutral.get)
          } else if (numArgs == 1) {
            compileExpression(args(0))
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
                (compileExpression(args(0)), compileExpression(Application(bo, args.tail)))
              } else {
                (compileExpression(Application(bo, args.init)), compileExpression(args.last))
              }
            } else {
              (compileExpression(args(0)), compileExpression(args(1)))
            }

            val op_result = IrVar(IrIntType.I64, fresh("op_result"))
            ctx.emit(IrBinOp(op_result, irOp, left, right))
            op_result
          }
      }
      case o: OpenRef => applyField(compileExpression(o), args)
      case o: ClosedRef => applyField(compileExpression(o), args)
      case o: OwnedExpr => applyField(compileExpression(o), args)
      case o: VarRef => applyField(compileExpression(o), args)
    }
    case o: OpenRef => loadOpenRef(o)
    case r: ClosedRef => loadFromPointer(loadClosedRef(r), fresh(r.name))
    case o: OwnedExpr => loadFromPointer(loadOwnedExpr(o), fresh("owned"))
    case o: VarRef => loadVarRef(o)
    case Lambda(ins, body, _) => val prevCtx = ctx
      ctx = new FunctionContext
      ctx.insertBlock(ctx.newBlock("entry"))
      val params = ins.variables.reverse
      val arguments = params.map(v => IrArgument(llvmType(v.tp), v.name))

      scopes ::= VariableScope()
      arguments.foreach { a =>
        val allocatedVar = IrVar(IrPtrType(a.tp), fresh(s"alloc_arg_${a.name}"))
        ctx.emitFirst(IrAlloca(allocatedVar))

        scopes.head.variables ::= Variable(a.name, allocatedVar)
        ctx.emit(IrStore(a, allocatedVar))
      }

      val result = compileExpression(body)(gc.append(ins))
      scopes = scopes.tail

      ctx.emit(IrReturn(result))

      val lambdaFun = IrFun(fresh("lambda"), IrFunType(result.tp, params.map(v => llvmType(v.tp))), arguments, ctx.buildBlocks())
      functions += lambdaFun
      ctx = prevCtx
      IrFunctionRef(lambdaFun)
    case Block(exprs) =>
      scopes ::= VariableScope()
      val result = if (exprs.nonEmpty) {
        exprs.dropRight(1).foreach { e => compileExpression(e) }
        compileExpression(exprs.last)
      } else {
        // dummy value (Unit.Value)
        compileExpression(Unit.Value)
      }
      scopes = scopes.tail
      result
    case Return(exp, false) =>
      val value = compileExpression(exp)
      ctx.emit(value.tp match {
        case IrVoidType => IrReturnVoid
        case _ => IrReturn(value)
      })
      compileExpression(Unit.Value)
    case e@EVarDecl(_, _, dfO, _, _) => bindDeclaration(e, dfO.map(compileExpression))
    case Assign(target, value) =>
      compileAssignment(target, compileExpression(value))
      compileExpression(Unit.Value)
    case Instance(theory) => val theoryPath = mainTheoryPath(theory)
      val module = gc.lookupGlobal(theoryPath).get.asInstanceOf[Module]
      val exprDecls = module.decls.collect { case d: ExprDecl => d }
      val struct = IrStruct(theoryPath.toString, exprDecls.map { d => llvmType(d.tp) })
      val size = IrVar(IrIntType.I64, fresh("size"))
      ctx.emit(IrComputeSize(size, struct))

      val structPtr = IrVar(IrPtrType(struct), fresh("struct_ptr"))
      ctx.emit(IrCall(Some(structPtr), IrFunctionRef(SpecialFunctions.mallocFun), List(size)))
      val initFun = IrDeclFun(s"${theoryPath}_initialize", IrFunType(IrVoidType, Nil))
      ctx.emit(IrCall(None, IrFunctionRef(initFun), List(structPtr)))

      // Initializes the expression declared by this instance
      theory.decls.foreach { case ExprDecl(name, _, _, Some(exp), _, _) => val fieldIndex = exprDecls.indexWhere(_
        .name == name)
        storeField(struct, structPtr, compileExpression(exp), fieldIndex)
      case _ =>
      }

      structPtr
    case Tuple(comps) =>
      val values = comps.map(compileExpression)
      val struct = findProdStruct(values.map(a => a.tp))
      val size = IrVar(IrIntType.I64, fresh("size"))
      ctx.emit(IrComputeSize(size, struct))

      val structPtr = IrVar(IrPtrType(struct), fresh("struct_ptr"))
      ctx.emit(IrCall(Some(structPtr), IrFunctionRef(SpecialFunctions.mallocFun), List(size)))

      // Initializes the tuple values
      values.zipWithIndex.foreach { case (vl, fieldIndex) => storeField(struct, structPtr, vl, fieldIndex)}
      structPtr
    case Projection(tuple, index) =>
      val structPtr = compileExpression(tuple)
      val struct = structPtr.tp match {
        case IrPtrType(s: IrStruct) => s
      }
      // Projection indices start at 1, but llvm struct fields are 0 indexed
      loadField(struct, structPtr, index - 1)
    case Match(e, cases, false) =>
      val target = compileExpression(e)
      val endB = ctx.newBlock("end")

      var tp: IrType = IrUnknownType
      val allocMatchResult = IrVar(IrPtrType(tp), fresh("alloc_match_result"))
      ctx.emitFirst(IrAlloca(allocMatchResult))

      cases.zipWithIndex.foreach { case (MatchCase(context, pattern, body), index)  =>
        scopes ::= VariableScope()
        // Pattern variables, which will be assigned in compileMatch
        context.decls.foreach { case vd: EVarDecl => bindDeclaration(vd, None) }
        val bindings = context.decls.collect { case vd: EVarDecl => vd.name }.toSet

        val nextMatchB = if (index == cases.length - 1) endB else ctx.newBlock("next_match")
        val matchedB = ctx.newBlock("matched")
        ctx.emit(IrCondBranch(compileMatch(pattern, target, bindings), matchedB.label, nextMatchB.label))
        ctx.insertBlock(matchedB)

        val matchResult = compileExpression(body)
        tp = matchResult.tp
        ctx.emit(IrStore(matchResult, allocMatchResult))

        ctx.emit(IRBranch(endB.label))

        scopes = scopes.tail
        ctx.insertBlock(nextMatchB)
      }

      val result = IrVar(tp, fresh("result"))
      ctx.emit(IrLoad(result, allocMatchResult))

      result
  }

  // Compiler equivalent of Interpreter.interpretDynamicBoolean.
  private def compileDynamicBoolean(exp: Expression)(implicit gc: GlobalContext): IrValue = exp match {
    case Assign(target, value) => compileMatch(target, compileExpression(value))
    case _ => compileExpression(exp)
  }

  private def compileAssignment(target: Expression, value: IrValue)(implicit gc: GlobalContext): Unit = target match {
    case VarRef(name) => ctx.emit(IrStore(value, getAllocatedVariable(name)))
    case vd: EVarDecl => bindDeclaration(vd, Some(value))
    case Tuple(components) =>
      val struct = tupleStruct(value)
      components.zipWithIndex.foreach { case (component, index) =>
        compileAssignment(component, loadField(struct, value, index))
      }
    case _ => ???
  }

  // Matches the value of the target expression against the value. Returns true if they match
  // This may bind new variables to the target expression.
  private def compileMatch(target: Expression, value: IrValue, bindings: Set[String] = Set.empty)
    (implicit gc: GlobalContext): IrValue = target match {
    case VarRef(name) if bindings.contains(name) =>
      // n is pattern-variable
      ctx.emit(IrStore(value, getAllocatedVariable(name)))
      IrConst(true)
    case VarRef(name) =>
      val current = loadVarRef(VarRef(name))
      // TODO String comparison is not supported yet
      compileIntCompare(current, value)
    case vd: EVarDecl =>
      bindDeclaration(vd, Some(value))
      IrConst(true)
    case Tuple(components) =>
      val struct = tupleStruct(value)
      components.zipWithIndex
        .map { case (component, index) => compileMatch(component, loadField(struct, value, index), bindings) }
        .foldLeft[IrValue](IrConst(true))(compileBooleanAnd)
    case nv: NumberValue =>
      val current = compileExpression(nv)
      compileIntCompare(current, value)
    case _ => ???
  }

  private def compileBooleanAnd(left: IrValue, right: IrValue): IrValue = {
    val result = IrVar(IrIntType.I1, fresh("bool_and"))
    ctx.emit(IrBinOp(result, IAND, left, right))
    result
  }

  private def compileIntCompare(left: IrValue, right: IrValue): IrValue = {
    val result = IrVar(IrIntType.I1, fresh("int_compare"))
    ctx.emit(IrICmp(result, EQUAL, left, right))
    result
  }

  private def bindDeclaration(vd: EVarDecl, value: Option[IrValue]): IrVar = {
    val allocatedVar = IrVar(IrPtrType(llvmType(vd.tp)), fresh(s"alloc_${vd.name}"))
    ctx.emitFirst(IrAlloca(allocatedVar))
    scopes.head.variables ::= Variable(vd.name, allocatedVar)
    value.foreach(v => ctx.emit(IrStore(v, allocatedVar)))
    allocatedVar
  }

  private def tupleStruct(value: IrValue): IrStruct = value.tp match {
    case IrPtrType(struct: IrStruct) => struct
    case _ => ???
  }

  private def applyField(fieldVar: IrValue, args: List[Expression])(implicit gc: GlobalContext): IrVar = {
    val result = IrVar(fieldVar.tp.asInstanceOf[IrFunType].ret, fresh("result"))

    val option = result.tp match {
      case IrVoidType => None
      case _ => Some(result)
    }

    ctx.emit(IrCall(option, fieldVar, args.map(a => compileExpression(a))))
    result
  }

  private def compileDeclaration(d: Declaration)(implicit gc: GlobalContext): Unit = {
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

  private def storeField(struct: IrStruct, structPtr: IrValue, op: IrValue, fieldIndex: Int): Unit = {
    val fieldPtr = getFieldPointer(struct, structPtr, fieldIndex)
    ctx.emit(IrStore(op, fieldPtr))
  }

  private def loadField(struct: IrStruct, structPtr: IrValue, fieldIndex: Int): IrVar = {
    loadFromPointer(getFieldPointer(struct, structPtr, fieldIndex), fresh(s"field_$fieldIndex"))
  }

  private def getFieldPointer(struct: IrStruct, structPtr: IrValue, fieldIndex: Int): IrVar = {
    val fieldPtr = IrVar(IrPtrType(struct.fields(fieldIndex)), fresh(s"field_${fieldIndex}_ptr"))
    ctx.emit(IrGetElement(fieldPtr, struct, structPtr, List(0, fieldIndex)))
    fieldPtr
  }

  private def loadFromPointer(ptr: IrVar, name: String): IrVar = ptr.tp match {
    case IrPtrType(valueType) =>
      val value = IrVar(valueType, name)
      ctx.emit(IrLoad(value, ptr))
      value
    case _ => throw new IllegalArgumentException(s"Expected a pointer, found ${ptr.tp}")
  }

  private def compileModule(df: TheoryValue, closed: Boolean, moduleName: String, gcI: GlobalContext): Unit = { //
    // Recursively traverse other declarations
    // We need to do this before traversing all expression declarations in the current module to prevent inner
    // modules from messing with the function context
    df.decls.foreach { case _: ExprDecl =>
    case _: Include =>
    case d => compileDeclaration(d)(gcI)
    }

    val exprDecls = df.decls.collect { case d: ExprDecl => d }
    val struct = IrStruct(moduleName, exprDecls.map { d => llvmType(d.tp) })
    structs += struct

    if (closed) { // Function to initialize all struct fields
      ctx = new FunctionContext
      val structArg = IrArgument(IrPtrType(struct), "__instance")
      ctx.insertBlock(ctx.newBlock("entry"))

      df.decls.foreach { case e@ExprDecl(_, _, _, Some(exp), _, _) => val fieldIndex = exprDecls.indexOf(e)
        storeField(struct, structArg, compileExpression(exp)(gcI), fieldIndex)
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
        storeField(struct, structGlobal, compileExpression(exp)(gcI), fieldIndex)
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

  private def loadClosedRef(r: ClosedRef)(implicit gc: GlobalContext): IrVar = {
    val theoryPath = gc.currentParent
    val module = gc.lookupGlobal(theoryPath).get.asInstanceOf[Module]
    val exprDecls = module.decls.collect { case d: ExprDecl => d }
    val fieldIndex = exprDecls.indexWhere(_.name == r.name)
    val struct = IrStruct(theoryPath.toString, exprDecls.map(d => llvmType(d.tp)))
    getFieldPointer(struct, IrArgument(IrPtrType(struct), "__instance"), fieldIndex)
  }

  private def loadOwnedExpr(o: OwnedExpr)(implicit gc: GlobalContext): IrVar = {
    o match {
      case OwnedExpr(owner, ownerDom, ClosedRef(name)) =>
        val theoryPath = mainTheoryPath(ownerDom)
        val module = gc.lookupGlobal(theoryPath).get.asInstanceOf[Module]
        val exprDecls = module.decls.collect { case d: ExprDecl => d }
        val fieldIndex = exprDecls.indexWhere(_.name == name)
        val struct = IrStruct(theoryPath.toString, exprDecls.map(d => llvmType(d.tp)))
        getFieldPointer(struct, compileExpression(owner), fieldIndex)
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

  private def loadVarRef(o: VarRef)(implicit gc: GlobalContext): IrValue = {
    val allocatedVariable = getAllocatedVariable(o.name)
    allocatedVariable.tp match {
      case tp: IrPtrType => val result = IrVar(tp.to, fresh(o.name))
        ctx.emit(IrLoad(result, allocatedVariable))
        result
      case _ => ???
    }
  }

  private def loadBuiltin(name: String): IrFun = {
    val definition = builtins.Builtins.find(x => x.name == name)
      .getOrElse(throw new NotImplementedError(s"builtin $name doesn't have a signature"))

    //declare llvm builtin
    if(!functions.exists(x => x.name == definition.llvmName)) {
      val (decl, fun) = definition.generateFunction()
      //add function to lists
      declaredFunctions.append(decl)
      functions.append(fun)

      fun
    }else{
      functions.find(x => x.name == definition.llvmName).getOrElse(throw new NotImplementedError())
    }
  }


  private def llvmType(tp: Type): IrType = {
    tp match {
      case BoolType => IrIntType.I1
      case _: NumberType => IrIntType.I64
      case FunType(ins, out) => IrFunType(llvmType(out), ins.variables.map(v => llvmType(v.tp)))
      case ClassType(dom) => IrPtrType(IrStruct(mainTheoryPath(dom).toString, Nil))
      case ProdType(ExprContext(Nil)) => IrVoidType
      case u: UnknownType if u.known => llvmType(u.skipUnknown)
      case StringType => IrPtrType(IrConstChar(0))
      case ProdType(c) => IrPtrType(findProdStruct(c.variables.reverse.map(v => llvmType(v.tp))))
      case OwnedType(_, _, owned) => llvmType(owned)
      case _ => throw new IllegalArgumentException(s"Unsupported type: $tp")
    }
  }

  private def reduceTypeInfo(tp: IrType) = tp match {
    case _: IrPtrType => IrPtrType(IrUnknownType)
    case _: IrFunType => IrPtrType(IrUnknownType)
    case _ => tp
  }

  private def findProdStruct(types: List[IrType]): IrStruct = {
    // We reduce the type pointer type information to treat all pointers the same.
    // We don't need to create different structs for them.
    val reduced = types.map(reduceTypeInfo)

    val name = prodStructName.getOrElseUpdate(reduced, {
      val freshName = fresh("__prod_type")
      structs += IrStruct(freshName, reduced)
      freshName
    })

    // The struct we return should use the original types, because this type info is still useful during IR generation.
    IrStruct(name, types)
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