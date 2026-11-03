package info.kwarc.p.compiler

import info.kwarc.p.{Plus, _}
import info.kwarc.p.compiler.Condition._
import info.kwarc.p.compiler.IRGenerator.TOP_LEVEL_STRUCT_NAME
import info.kwarc.p.compiler.Operation._

import scala.collection.mutable

object IRGenerator {
  private val TOP_LEVEL_STRUCT_NAME = "__top_level"
  private val IGNORED_DECLARATION: ExprDecl => Boolean = d => d.tp match { case _: ProofType => true case _ => false }

  def run(p: Program): IrProgram = {
    val ig = new IRGenerator()

    val gc = GlobalContext(p.voc)
    ig.compileModule(Module("", closed = false, p.voc))(gc)
    if (p.main != Unit.Value) {
      ig.compileMain(p.main)(gc)
    }

    IrProgram(ig.declaredFunctions, ig.structs.toList, ig.globals.toList, ig.functions.toList)
  }
}

case class Variable(name: String, irVar: IrVar, mutable: Boolean)

case class RegionalEnvironment(name: String, region: Option[IrVar] = None, local: LocalEnvironment = LocalEnvironment.empty, parent: Option[RegionalEnvironment] = None) {
  def allocate(n: String, vl: IrVar, mutable: Boolean = true): Unit = {
    if (!vl.tp.isInstanceOf[IrPtrType] && mutable) throw new RuntimeException(s"Mutable variable $n is not a pointer")
    local.fields ::= Variable(n, vl, mutable)
  }

  def inNewBlock[A](a: => A): A = {
    val prevFields = local.fields
    try {a}
    finally {
      local.fields = prevFields
    }
  }
}

case class LocalEnvironment(var fields: List[Variable]) {
  def getO(n: String) = fields.find(_.name == n)
}

object LocalEnvironment {
  def empty = LocalEnvironment(Nil)
}

object SpecialFunctions {
  val malloc = IrDeclFun("malloc", IrFunType(IrPtrType(IrIntType.I64), List(IrIntType.I64)))

  val theoryCreate = IrDeclFun("theory_create", IrFunType(IrPtrType(), List(IrIntType.I64, IrPtrType())))
  val theoryInitField = IrDeclFun("theory_init_field", IrFunType(IrVoidType, List(IrPtrType(), IrPtrType(), IrPtrType())))
  val theoryGetField = IrDeclFun("theory_get_field", IrFunType(IrPtrType(), List(IrPtrType(), IrPtrType())))

  val stdin = IrGlobalExtern("stdin", IrPtrType(null))
}

object SpecialStructs {
  // {fun_ptr, env_ptr}
  val lambda = IrStruct("lambda", List(IrFunType(IrPtrType(), List(IrPtrType())), IrPtrType()))
}

private object TypeExpansion extends StatelessTraverser {

  override def apply(tp: Type)(implicit gc: GlobalContext, a: Unit): Type = tp match {
    case MaybeAppliedRef(r, tpArgs, expArgs) =>
      gc.lookupRef(r) match {
        case Some(td: TypeDecl) =>
          td.dfO match {
            case Some(df) =>
              val sub = td.params.substitute(tpArgs ::: expArgs)
              apply(df.substituteInType(sub))
            case None =>
              MaybeAppliedRef(r, tpArgs.map(apply), expArgs)
          }
        case Some(_: TVarDecl) if tpArgs.isEmpty && expArgs.isEmpty => r
        case _ => applyDefault(tp)
      }

    case ct: ClassType => ct
    case _ => applyDefault(tp)
  }
}


private class IRGenerator {

  private val declaredFunctions: mutable.ArrayBuffer[IrDeclFun] = mutable.ArrayBuffer(
    SpecialFunctions.malloc,
    SpecialFunctions.theoryCreate, SpecialFunctions.theoryInitField, SpecialFunctions.theoryGetField
  )

  private val globals: mutable.ArrayBuffer[IrGlobalValue] = mutable.ArrayBuffer(SpecialFunctions.stdin)
  private val structs: mutable.ArrayBuffer[IrStruct] = mutable.ArrayBuffer(SpecialStructs.lambda)
  private val functions: mutable.ArrayBuffer[IrFun] = mutable.ArrayBuffer()

  private val nameCount: mutable.Map[String, Int] = mutable.Map().withDefaultValue(0)
  private val prodStructName: mutable.Map[List[IrType], String] = mutable.Map()
  private val stringGlobals: mutable.Map[String, IrGlobal] = mutable.Map()
  private val closureAdapters = mutable.Map[String, IrFun]()
  private var regions = List(RegionalEnvironment("toplevel"))
  private def frame = regions.head

  private val checker = new Checker(ErrorThrower)
  private var ctx: FunctionContext = _

  private def lookupLocalO(n: String): Option[Variable] = {
    var reg = regions.headOption
    while (reg.nonEmpty) {
      reg.get.local.getO(n) match {
        case Some(variable) => return Some(variable)
        case None => reg = reg.get.parent
      }
    }
    None
  }

  private def lookupLocal(n: String): Variable = lookupLocalO(n).getOrElse(throw new RuntimeException(s"Variable $n " +
    s"not found"))

  def compileMain(exp: Expression)(implicit gc: GlobalContext): Unit = {
    inNewFunctionCtx {
      val value = compileExpression(exp)(gc)
      ctx.emit(IrReturn(value))

      // We require that the main expression evaluates to a 64-bit integer.
      val mainFun = IrFun("main", IrFunType(IrIntType.I64, Nil), Nil, ctx.buildBlocks())
      functions += mainFun
    }
  }

  /** Compiles an expression
   * All instructions will be inserted into the current block / function context.
   *
   * @param exp Expression to compile
   * @return IrValue representing the result of the expression. */
  private def compileExpression(exp: Expression)(implicit gc: GlobalContext): IrValue = exp match {
    // treated as i64 integers.
    case NumberValue(tp, re, _) =>  tp match {
      case NumberType.Int => IrConst(re.asInstanceOf[Rat].enu.toInt)
      case NumberType.Float => IrConst(re.asInstanceOf[ApproxReal].value)
      case NumberType.Rat=>
        val num = re.asInstanceOf[Rat]
        val initializer = fresh("rational_init")
        val g = IrGlobal(initializer, rationalNumbers.decl, Some(s"{i64 ${num.enu.longValue}, i64 ${num.deno.longValue} }"))
        globals.append(g)
        if (!structs.exists(x => x.name == rationalNumbers.decl.name)){
          //memset
          declaredFunctions.append(IrDeclFun("llvm.memcpy.inline.p0.p0.i64",
            IrFunType(IrVoidType, List(IrPtrType(null), IrPtrType(null), IrIntType.I64, IrIntType.I1))))

          structs.append(rationalNumbers.decl)
          rationalNumbers.functions.foreach(x => functions.append(x._2))
        }
        IrRational(num.enu.longValue, num.deno.longValue, initializer)
      }

     // Booleans are represented using i1 integers.
    case BoolValue(value) => IrConst(value)
    case StringValue(value) =>
      stringGlobals.getOrElseUpdate(value, {
        val v = IrGlobal(fresh("name"), IrConstChar(value.length), Some(s"c\"$value\\00\""))
        globals.append(v)
        v
      })
    // Unit value is represented as a special constant to make it easy to
    // spot when debugging
    case Unit.Value => IrConst(0xdeadbeef) // note that Unit.Value is defined
    case IfThenElse(cond, thn, elsO) =>
      compileIfThenElse(cond, thn, elsO)
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

            val (left, right) = if (numArgs > 2) {
              if (inf.assoc == RightAssociative) {
                (compileExpression(args(0)), compileExpression(Application(bo, args.tail)))
              } else {
                (compileExpression(Application(bo, args.init)), compileExpression(args.last))
              }
            } else {
              (compileExpression(args(0)), compileExpression(args(1)))
            }

            var op_result: IrVar = null

            def emitOp(l: IrValue, r: IrValue): Unit = {
              val irOp = inf match {
                case Plus => FADD
                case Minus => FSUB
                case Times => FMUL
                case Divide => FDIV
              }
              ctx.emit(IrBinOp(op_result, irOp, l, r))
            }

            (checker.inferCheckedExpression(gc, args(0)), checker.inferCheckedExpression(gc, args(1))) match {
              case (NumberType.Rat, NumberType.Rat) =>
                op_result = IrVar(IrStructTyped("", List(IrIntType.I64, IrIntType.I64)), fresh("op_result"))
                inf match {
                  case Plus => ctx.emit(IrCall(Some(op_result), IrFunctionRef(rationalNumbers.add()._2), List(left,right)))
                  case Minus =>
                    val op_temp = IrVar(IrStructTyped("", List(IrIntType.I64, IrIntType.I64)), fresh("op_tmp"))
                    ctx.emit(IrCall(Some(op_temp), IrFunctionRef(rationalNumbers.negate()._2), List(right)))
                    ctx.emit(IrCall(Some(op_result), IrFunctionRef(rationalNumbers.add()._2), List(left,op_temp)))
                  case Times => ctx.emit(IrCall(Some(op_result), IrFunctionRef(rationalNumbers.mul()._2), List(left,right)))
                  case Divide =>
                    val op_temp = IrVar(IrStructTyped("", List(IrIntType.I64, IrIntType.I64)), fresh("op_tmp"))
                    ctx.emit(IrCall(Some(op_temp), IrFunctionRef(rationalNumbers.invert()._2), List(left,right)))
                    ctx.emit(IrCall(Some(op_result), IrFunctionRef(rationalNumbers.mul()._2), List(left,op_temp)))
                }
              case (NumberType.Rat, _) =>
              case (_, NumberType.Rat) =>
              case (NumberType.Float, NumberType.Float) =>
                op_result = IrVar(IrFloat64(), fresh("op_result"))
               emitOp(left, right)
              case (NumberType.Float, _) =>
                val conv = IrVar(IrFloat64(), fresh("conv"))
                ctx.emit(IrConvert(right, conv))
                op_result = IrVar(IrFloat64(), fresh("op_result"))
                emitOp(left, conv)
              case (_, NumberType.Float) =>
                val conv = IrVar(IrFloat64(), fresh("conv"))
                ctx.emit(IrConvert(left, conv))
                op_result = IrVar(IrFloat64(), fresh("op_result"))
                emitOp(conv, right)
              case _ =>
                val irOp = inf match {
                  case Plus => IADD
                  case Minus => ISUB
                  case Times => IMUL
                  case Divide => IDIV
                }
                op_result = IrVar(IrIntType.I64, fresh("op_result"))
                ctx.emit(IrBinOp(op_result, irOp, left, right))
            }

            op_result
          }
      }
      case r => applyLambda(compileExpression(r), args.map(compileExpression))
    }
    case o: OpenRef => loadOpenRef(o)
    case r: ClosedRef => loadClosedRef(r)
    case OwnedExpr(own, dom, e) =>
      val instPtr = compileExpression(own)
      val re = RegionalEnvironment(own.toString, Some(instPtr.asInstanceOf[IrVar]))
      inFrame(re) {
        compileExpression(e)(gc.push(dom, Some(own)))
      }
    case o: VarRef => loadVarRef(o)
    case Lambda(ins, body, _) =>
      // Store all captured variables (and optionally the region)
      // TODO proper traverser, that also collects ClosedRef and This usage for regions
      val freeVariable = FreeVariables.collect(gc, exp, infer = true)
      val captured = freeVariable.zip(freeVariable.map(lookupLocal))

      val inRegion = frame.region.isDefined

      val ptrSize = IrVar(IrIntType.I64, fresh("ptrSize"))
      ctx.emit(IrComputeSize(ptrSize, IrPtrType()))
      val envPtr = IrVar(IrPtrType(), fresh("env_ptr"))
      val envSize = IrVar(IrIntType.I64, fresh("env_size"))

      ctx.emit(IrBinOp(envSize, IMUL, ptrSize, IrConst(captured.length + (if (inRegion) 1 else 0))))
      ctx.emit(IrCall(Some(envPtr), IrFunctionRef(SpecialFunctions.malloc), List(envSize)))

      captured.zipWithIndex.foreach { case ((_, variable), i) =>
        val fieldPtr = IrVar(IrPtrType(variable.irVar.tp), fresh(s"env_field${i}_ptr"))
        ctx.emit(IrGetElement(fieldPtr, IrPtrType(), envPtr, List(i)))
        ctx.emit(IrStore(variable.irVar, fieldPtr))
      }
      if (inRegion) {
        val regionPtr = IrVar(IrPtrType(), fresh("region_ptr"))
        ctx.emit(IrGetElement(regionPtr, IrPtrType(), envPtr, List(captured.length)))
        ctx.emit(IrStore(frame.region.get, regionPtr))
      }

      val lambdaFun = inNewFunctionCtx {
        // Rebuild the frame from the environment pointer
        val envPtrArg = IrVar(IrPtrType(), fresh("env_ptr_arg"))
        val lambdaRegion = if (inRegion) {
          val region = IrVar(IrPtrType(), fresh("region"))
          val regionPtr = IrVar(IrPtrType(), fresh("region_ptr"))
          ctx.emit(IrGetElement(regionPtr, IrPtrType(), envPtrArg, List(captured.length)))
          ctx.emit(IrLoad(region, regionPtr))
          Some(region)
        } else {
          None
        }

        val re = RegionalEnvironment("lambda", lambdaRegion)

        captured.zipWithIndex.foreach { case ((name, variable), i) =>
          val envField = IrVar(variable.irVar.tp, fresh(s"env_field$i"))
          val fieldPtr = IrVar(IrPtrType(variable.irVar.tp), fresh(s"env_field${i}_ptr"))
          ctx.emit(IrGetElement(fieldPtr, IrPtrType(), envPtrArg, List(i)))
          ctx.emit(IrLoad(envField, fieldPtr))

          re.allocate(name, envField, variable.mutable)
        }

        val params = ins.variables.reverse
        val arguments = params.map(v => IrVar(llvmType(v.tp), v.name))

        params.map(_.name).zip(arguments).foreach { case (name, arg) =>
          re.allocate(name, arg, mutable = false)
        }

        val result = inFrame(re) {
          compileExpression(body)(gc.append(ins))
        }

        ctx.emit(IrReturn(result))

        IrFun(fresh("lambda"), IrFunType(result.tp, IrPtrType() :: params.map(v => llvmType(v.tp))), envPtrArg :: arguments, ctx.buildBlocks())
      }
      functions += lambdaFun

      val structPtr = mallocStruct(SpecialStructs.lambda)
      storeField(SpecialStructs.lambda, structPtr, IrFunctionRef(lambdaFun), 0)
      storeField(SpecialStructs.lambda, structPtr, envPtr, 1)
      structPtr
    case Block(exprs) =>
      frame.inNewBlock {
        var gcI = gc
        val result = if (exprs.nonEmpty) {
          exprs.dropRight(1).foreach { e =>
            compileExpression(e)(gcI)
            gcI = gcI.append(LocalContext.collectContext(e))
          }
          compileExpression(exprs.last)(gcI)
        } else {
          // dummy value (Unit.Value)
          compileExpression(Unit.Value)
        }
        result
      }
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
    // TODO case inst: Instance if inst.isRuntime =>
    case Instance(concreteTheory) =>
      val gcI = gc.enter(concreteTheory)

      val fields = instanceFields(concreteTheory)
      val names = fields.map(f => compileExpression(StringValue(f.name)))

      val namesInit = names.map(_.renderWithType()).mkString("[", ", ", "]")

      val namesArray = IrGlobal(
        fresh("field_names"),
        IrArrayType(names.length, IrPtrType()),
        Some(namesInit)
      )
      globals += namesArray

      val theoryPtr = IrVar(
        IrPtrType(),
        fresh("theory")
      )

      ctx.emit(IrCall(
        Some(theoryPtr),
        IrFunctionRef(SpecialFunctions.theoryCreate),
        List(IrConst(fields.length.toLong), namesArray)
      ))

      // Initializes the expression declared by this instance
      val re = RegionalEnvironment("new instance", Some(theoryPtr))
      inFrame(re) {
        fields.foreach { field =>
          val valuePtr = boxValue(compileExpression(field.dfO.get)(gcI), fresh(s"value_ptr_${field.name}"))
          ctx.emit(IrCall(
            None,
            IrFunctionRef(SpecialFunctions.theoryInitField),
            List(theoryPtr, compileExpression(StringValue(field.name)), valuePtr)
          ))
        }
      }
      theoryPtr
    case Tuple(comps) =>
      val values = comps.map(compileExpression)
      val struct = findProdStruct(values.map(a => a.tp))
      val structPtr = mallocStruct(struct)

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
        frame.inNewBlock {
          val gcI = gc.append(context)
          // Pattern variables, which will be assigned in compileMatch
          context.decls.foreach { case vd: EVarDecl => bindDeclaration(vd, None)(gcI) }
          val bindings = context.decls.collect { case vd: EVarDecl => vd.name }.toSet

          val nextMatchB = if (index == cases.length - 1) endB else ctx.newBlock("next_match")
          val matchedB = ctx.newBlock("matched")
          ctx.emit(IrCondBranch(compileMatch(pattern, target, bindings)(gcI), matchedB.label, nextMatchB.label))
          ctx.insertBlock(matchedB)

          val matchResult = compileExpression(body)(gcI)
          tp = matchResult.tp
          ctx.emit(IrStore(matchResult, allocMatchResult))

          ctx.emit(IRBranch(endB.label))
          ctx.insertBlock(nextMatchB)
        }
      }

      val result = IrVar(tp, fresh("result"))
      ctx.emit(IrLoad(result, allocMatchResult))

      result
  }

  private def compileIfThenElse(cond: Expression, thn: Expression, elsO: Option[Expression])(implicit gc: GlobalContext): IrValue = {
    // TODO frame.inNewBlock for then block
    // Based on ideas from
    // https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl05.html#if-then-else
    val thenB = ctx.newBlock("then")
    val elseB = elsO.map(_ => ctx.newBlock("else"))
    val endB = ctx.newBlock("end")

    ctx.emit(IrCondBranch(compileDynamicBoolean(cond), thenB.label, elseB.map(_.label).getOrElse(endB.label)))

    ctx.insertBlock(thenB)
    val gcT = gc.append(LocalContext.collectContext(cond))
    val thnO = compileExpression(thn)(gcT)
    val allocResult = IrVar(IrPtrType(thnO.tp), fresh("alloc_result"))
    ctx.emit(IrStore(thnO, allocResult))
    ctx.emit(IRBranch(endB.label))

    elseB.zip(elsO).foreach { case (block, els) =>
      ctx.insertBlock(block)
      ctx.emit(IrStore(compileExpression(els), allocResult))
      ctx.emit(IRBranch(endB.label))
    }

    ctx.insertBlock(endB)
    ctx.emitFirst(IrAlloca(allocResult))
    val result = IrVar(thnO.tp, fresh("result"))
    ctx.emit(IrLoad(result, allocResult))
    result
  }

  // Compiler equivalent of Interpreter.interpretDynamicBoolean.
  private def compileDynamicBoolean(exp: Expression)(implicit gc: GlobalContext): IrValue = exp match {
    case Assign(target, value) => compileMatch(target, compileExpression(value))
    case _ => compileExpression(exp)
  }

  private def compileAssignment(target: Expression, value: IrValue)(implicit gc: GlobalContext): Unit = target match {
    case VarRef(name) => storeInVariable(lookupLocal(name), value)
    case vd: EVarDecl => bindDeclaration(vd, Some(value))
    case ClosedRef(n) =>
      frame.region match {
        case Some(theoryHeaderPtr) =>
          val fieldValuePtr = IrVar(IrPtrType(), fresh(s"field_value_ptr"))
          ctx.emit(IrCall(Some(fieldValuePtr), IrFunctionRef(SpecialFunctions.theoryGetField), List(theoryHeaderPtr, compileExpression(StringValue(n)))))
          ctx.emit(IrStore(value, fieldValuePtr))
        case None => throw new IllegalArgumentException("ClosedRef must be in a region")
      }
    case OwnedExpr(own, dom, e) =>
      val instPtr = compileExpression(own)
      val re = RegionalEnvironment(own.toString, Some(instPtr.asInstanceOf[IrVar]))
      inFrame(re) {
        compileAssignment(e, value)(gc.push(dom, Some(own)))
      }
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
      storeInVariable(lookupLocal(name), value)
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

  // TODO do not malloc immutable variables
  private def bindDeclaration(vd: EVarDecl, value: Option[IrValue])(implicit gc: GlobalContext): IrVar = {
    val size = IrVar(IrIntType.I64, fresh("size"))
    ctx.emit(IrComputeSize(size, llvmType(vd.tp)))

    val ptr = IrVar(IrPtrType(llvmType(vd.tp)), fresh(s"var_${vd.name}"))
    ctx.emit(IrCall(Some(ptr), IrFunctionRef(SpecialFunctions.malloc), List(size)))
    value.foreach(v => ctx.emit(IrStore(v, ptr)))
    frame.allocate(vd.name, ptr)
    ptr
  }

  private def tupleStruct(value: IrValue): IrStruct = value.tp match {
    case IrPtrType(struct: IrStruct) => struct
    case _ => ???
  }

  private def instanceFields(theory: Theory)(implicit gc: GlobalContext): List[ExprDecl] = {
    val fields = mutable.ArrayBuffer[ExprDecl]()
    val names = mutable.HashSet[String]()
    val includes = mutable.HashSet[Theory]()
    var todo = theory.decls
    while (todo.nonEmpty) {
      val d = todo.head
      todo = todo.tail
      d match {
        case field: ExprDecl if field.dfO.isDefined && names.add(field.name) =>
          fields += field
        case incl: Include if includes.add(incl.dom) =>
          todo = todo ::: Checker.evaluateTheory(gc, incl.dom).decls
        case _ =>
      }
    }
    fields.toList
  }

  private def applyLambda(structPtr: IrValue, args: List[IrValue])(implicit gc: GlobalContext): IrVar = {
    // structPtr should be a SpecialStructs.lambda holding {fun_ptr, env_ptr}
    structPtr.tp match {
      case IrPtrType(tp) => tp match {
        case struct@IrStruct("lambda", List(IrFunType(ret, _), _)) =>
          val result = IrVar(ret, fresh("result"))
          val option = result.tp match {
            case IrVoidType => None
            case _ => Some(result)
          }
          val funPtr = loadField(struct, structPtr, 0)
          val envPtr = loadField(struct, structPtr, 1)


          ctx.emit(IrCall(option, funPtr, envPtr :: args))
          result
      }
    }
  }

  private def applyFunction(functionRef: IrFunctionRef, args: List[IrValue]): IrVar = {
    val result = IrVar(functionRef.tp.ret, fresh("result"))
    val option = result.tp match {
      case IrVoidType => None
      case _ => Some(result)
    }

    ctx.emit(IrCall(option, functionRef, args))
    result
  }

  private def storeInVariable(variable: Variable, value: IrValue): Unit = {
    if (!variable.mutable) throw new IllegalArgumentException(s"Variable ${variable.name} is not mutable")
    ctx.emit(IrStore(value, variable.irVar))
  }

  private def loadVariable(variable: Variable): IrValue = {
    variable.irVar.tp match {
      case tp: IrPtrType if variable.mutable => val result = IrVar(tp.to, fresh(variable.name))
        ctx.emit(IrLoad(result, variable.irVar))
        result
      case _ if !variable.mutable => variable.irVar
    }
  }

  private def compileDeclaration(d: Declaration)(implicit gc: GlobalContext): Unit = {
    d match {
      case _: TypeDecl =>
      case m: Module =>
        compileModule(m)(gc.enter(m))
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

  // Stores the given value in heap allocated memory and returns a pointer to the memory
  private def boxValue(value: IrValue, name: String): IrVar = {
    val size = IrVar(IrIntType.I64, fresh("size"))
    ctx.emit(IrComputeSize(size, value.tp))

    val ptr = IrVar(IrPtrType(value.tp), fresh(name))
    ctx.emit(IrCall(Some(ptr), IrFunctionRef(SpecialFunctions.malloc), List(size)))
    ctx.emit(IrStore(value, ptr))
    ptr
  }

  private def loadField(struct: IrStruct, structPtr: IrValue, fieldIndex: Int): IrVar = {
    loadFromPointer(getFieldPointer(struct, structPtr, fieldIndex), fresh(s"${struct.name}_field$fieldIndex"))
  }

  private def getFieldPointer(struct: IrStruct, structPtr: IrValue, fieldIndex: Int): IrVar = {
    val fieldPtr = IrVar(IrPtrType(struct.fields(fieldIndex)), fresh(s"${struct.name}_field${fieldIndex}_ptr"))
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

  private def compileModule(module: Module)(implicit gc: GlobalContext): Unit = {
    val theory = mainTheoryPath(gc.theory)
    val moduleName = if (theory.isRoot) TOP_LEVEL_STRUCT_NAME else theory.toString
    // Recursively traverse other declarations
    // We need to do this before traversing all expression declarations in the current module to prevent inner
    // modules from messing with the function context
    module.df.decls.foreach { case _: ExprDecl =>
    case _: Include =>
    case d => compileDeclaration(d)
    }

    if (!module.closed) {
      module.df.decls.collect{case d: ExprDecl if d.dfO.isDefined => d}.foreach { expr =>
        val re = RegionalEnvironment(module.toString, None)
        inFrame(re) {
          inNewFunctionCtx {
            val result = compileExpression(expr.dfO.get)
            ctx.emit(IrReturn(result))
            val fun = IrFun(s"${moduleName}_${expr.name}", IrFunType(result.tp, Nil), Nil, ctx.buildBlocks())
            functions += fun
            IrFunctionRef(fun)
          }
        }
      }
    }
  }

  private def mallocStruct(struct: IrStruct): IrVar = {
    val size = IrVar(IrIntType.I64, fresh("size"))
    ctx.emit(IrComputeSize(size, struct))

    val structPtr = IrVar(IrPtrType(struct), fresh("struct_ptr"))
    ctx.emit(IrCall(Some(structPtr), IrFunctionRef(SpecialFunctions.malloc), List(size)))
    structPtr
  }

  private def loadClosedRef(r: ClosedRef)(implicit gc: GlobalContext): IrValue = {
    frame.region match {
      case Some(theoryHeaderPtr) =>
        gc.lookupRegional(r.name).map(d => TypeExpansion(gc, d)) match {
          case Some(ed: ExprDecl) =>
            // TODO When a value is loaded before it is initialized the Interpreter falls back to the defined value
            // see Interpreter.lookupRegional
            // test case: test/compiler/test/core/instance_mutable_closed_ref/main.pp
            val fieldType = llvmType(ed.tp)
            val fieldValuePtr = IrVar(IrPtrType(fieldType), fresh(s"field_value_ptr"))
            ctx.emit(IrCall(Some(fieldValuePtr), IrFunctionRef(SpecialFunctions.theoryGetField),
              List(theoryHeaderPtr, compileExpression(StringValue(r.name)))))
            loadFromPointer(fieldValuePtr, fresh(s"value_${r.name}"))
        }
      case None => throw new IllegalArgumentException("ClosedRef must be in a region")
    }
  }

  private def loadOpenRef(o: OpenRef)(implicit gc: GlobalContext): IrValue = {
    val path = o.path
    val modulePath = path.up
    //special case: generate IR for builtins
    if (path.head == "Uniformal") {
      val builtin = closureAdapter(loadBuiltin(path.names(1)))
      //builtin.signature
      val lambdaPtr = mallocStruct(SpecialStructs.lambda)
      storeField(SpecialStructs.lambda, lambdaPtr, IrFunctionRef(builtin), 0)
      storeField(SpecialStructs.lambda, lambdaPtr, IrNullValue, 1)

      return lambdaPtr
    }

    gc.lookupGlobal(path) match {
      case Some(d: ExprDecl) =>
        val moduleName = if (modulePath.isRoot) TOP_LEVEL_STRUCT_NAME else modulePath.toString
        applyFunction(IrFunctionRef(IrDeclFun(s"${moduleName}_${path.name}", IrFunType(llvmType(d.tp), Nil))), Nil)
    }
  }

  private def loadVarRef(o: VarRef)(implicit gc: GlobalContext): IrValue = {
    val variable = lookupLocal(o.name)
    loadVariable(variable)
  }

  private def closureAdapter(target: IrFunctionLike): IrFun = {
    closureAdapters.getOrElseUpdate(target.name, {
      val sig = target.signature
      val params = sig.params.zipWithIndex.map { case (tp, i) => IrVar(tp, s"arg$i") }
      val result = IrVar(sig.ret, "result")

      val call = IrCall(if (sig.ret == IrVoidType) None else Some(result), IrFunctionRef(target), params)
      val body = if (sig.ret == IrVoidType) List(call, IrReturnVoid) else List(call, IrReturn(result))
      val adapter = IrFun(s"${target.name}.closure", IrFunType(sig.ret, IrPtrType() :: sig.params),
        IrVar(IrPtrType(), "env") :: params, List(IrBlock("entry", body)))
      functions += adapter
      adapter
    })
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

  private def llvmType(tp: Type)(implicit gc: GlobalContext): IrType = {
    tp match {
      case BoolType => IrIntType.I1
      case _: NumberType => IrIntType.I64
      case FunType(ins, out) => IrPtrType(SpecialStructs.lambda.copy(fields = List(IrFunType(llvmType(out), ins.variables.map(v => llvmType(v.tp))), IrPtrType())))
      case _: ClassType => IrPtrType()
      case ProdType(ExprContext(Nil)) => IrVoidType
      case u: UnknownType if u.known => llvmType(u.skipUnknown)
      case StringType => IrPtrType(IrConstChar(0))
      case ProdType(c) => IrPtrType(findProdStruct(c.variables.reverse.map(v => llvmType(v.tp))))
      case OwnedType(_, _, owned) =>
        llvmType(owned)
      case _ => throw new IllegalArgumentException(s"Unsupported type: $tp")
    }
  }

  private def reduceTypeInfo(tp: IrType) = tp match {
    case _: IrPtrType => IrPtrType()
    case _: IrFunType => IrPtrType()
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

  private def mainTheoryPath(theory: Theory): Path = {
    // The first include of a theory should always be the 'class type'
    theory.decls match {
      case ::(Include(OpenRef(p), _, _), _) => p
      case _ =>  throw new IllegalArgumentException(s"Theory declarations doesn't start with include")
    }
  }

  private def inFrame[A](f: RegionalEnvironment)(a: => A) = {
    regions ::= f
    try {a}
    finally {regions = regions.tail}
  }

  private def inNewFunctionCtx[A](a: => A) = {
    val prevCtx = ctx
    ctx = new FunctionContext
    ctx.insertBlock(ctx.newBlock("entry"))
    try {a}
    finally {
      ctx = prevCtx
    }
  }

  private case class BlockBuilder(label: String, instructions: mutable.ArrayBuffer[IrInstr] = mutable.ArrayBuffer()) {
    def addFirst(i: IrInstr): Unit = instructions.prepend(i)

    def add(i: IrInstr): Unit = instructions += i

    def build() = IrBlock(label, instructions.toList)
  }

  private class FunctionContext {
    private val blocks = mutable.ArrayBuffer[BlockBuilder]()
    private var currentBlock: BlockBuilder = _

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
