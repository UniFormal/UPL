package info.kwarc.p.compiler

import info.kwarc.p.compiler.Operation.{IMUL, ISUB}

import scala.collection.mutable

case class IrProgram(declaredFunctions: mutable.ArrayBuffer[IrDeclFun], structs: List[IrStruct], globals: List[IrGlobalValue],
  functions: List[IrFun])

case class IrStruct(name: String, fields: List[IrType]) extends IrType {
  def renderStruct(): String = s"%$name = type { ${fields.map { f => f.render() }.mkString(", ")} }"

  override def render(): String = s"%$name"
}

trait IrFunctionLike {
  def name: String

  def signature: IrFunType

  def renderDecl(): String =
    s"""|declare ${signature.ret.render()} @$name(${
      signature.params.map(_.render()).mkString(", ")
    })""".stripMargin
}

case class IrDeclFun(name: String, signature: IrFunType) extends IrFunctionLike

case class IrFun(name: String, signature: IrFunType, params: List[IrVar], blocks: List[IrBlock]) extends
  IrFunctionLike {

  def renderFun(): String =
    s"""|define ${
      signature.ret.render()
    } @$name(${params.map(_.renderWithType()).mkString(", ")}) {
        |${blocks.map(_.render()).mkString("\n")}
        |}""".stripMargin
}

case class IrGlobal(name: String, tp2: IrType, init: Option[String] = None) extends IrGlobalValue {
  override def tp: IrType = IrPtrType(tp2)

  def renderGlobal(): String = s"@$name = global ${tp2.render()} ${init.getOrElse("zeroinitializer")}"

  override def render(): String = s"@$name"
}
/*external value declaration*/
case class IrGlobalExtern(name: String, tp: IrType) extends IrGlobalValue{

  def renderGlobal(): String = s"@$name = external global ${tp.render()}"
  override def render(): String = s"@$name"
}

case class IrBlock(label: String, instructions: List[IrInstr]) {
  def render(): String =
    s"""|$label:
        |${
      instructions.map(i => s"\t${i.render()}").mkString("\n")
    }""".stripMargin
}

sealed trait IrInstr {
  def render(): String
}

case class IrReturn(value: IrValue) extends IrInstr {
  override def render(): String = s"ret ${value.tp.render()} ${value.render()}"
}

object IrReturnVoid extends IrInstr {
  override def render(): String = s"ret void"
}

case class IrICmp(result: IrVar, cond: Condition, left: IrValue, right: IrValue) extends IrInstr {
  override def render(): String = s"${result.render()} = icmp ${cond.label} ${left.tp.render()} ${
    left.render()
  }, ${right.render()}"
}

sealed abstract class Condition(val label: String)

object Condition {
  case object EQUAL extends Condition("eq")
  case object NOT_EQUAL extends Condition("ne")
  case object SIGNED_GREATER_THAN extends Condition("sgt")
  case object SIGNED_GREATER_EQUAL extends Condition("sge")
  case object SIGNED_LESS_THAN extends Condition("slt")
  case object SIGNED_LESS_EQUAL extends Condition("sle")
}

case class IrBinOp(result: IrVar, op: Operation, left: IrValue, right: IrValue) extends IrInstr {
  override def render(): String = s"${result.render()} = ${op.label} ${left.tp.render()} ${left.render()}, ${right
    .render()}"
}

sealed abstract class Operation(val label: String)

object Operation {
  case object IADD extends Operation("add")
  case object IAND extends Operation("and")
  case object ISUB extends Operation("sub")
  case object IMUL extends Operation("mul")
  case object IDIV extends Operation("sdiv")
  case object FADD extends Operation("fadd")
  case object FSUB extends Operation("fsub")
  case object FMUL extends Operation("fmul")
  case object FDIV extends Operation("fdiv")
}

case class IrCondBranch(cond: IrValue, ifTrue: String, ifFalse: String) extends IrInstr {
  override def render() = s"br i1 ${cond.render()}, label %$ifTrue, label %$ifFalse"
}

case class IRBranch(dest: String) extends IrInstr {
  override def render() = s"br label %$dest"
}

case class IrGetElement(result: IrVar, struct: IrStruct, ptr: IrValue, vals: List[Int]) extends IrInstr {
  override def render(): String = s"${result.render()} = getelementptr ${struct.render()}, ${
    ptr.renderWithType()
  }, ${vals.map(v => s"i32 $v").mkString(", ")}"
}

case class IrComputeSize(result: IrVar, tp: IrType) extends IrInstr {
  override def render(): String = {
    s"${result.render()} = ptrtoint ptr getelementptr (${tp.render()}, ptr null, i32 1) to ${result.tp.render()}"
  }
}

case class IrAlloca(result: IrVar) extends IrInstr {
  override def render(): String = s"${result.render()} = alloca ${result.tp.render()}"
}

case class IrStore(op: IrValue, ptr: IrValue) extends IrInstr {
  override def render(): String = s"store ${op.tp.render()} ${op.render()}, ${ptr.renderWithType()}"
}

case class IrLoad(result: IrVar, ptr: IrValue) extends IrInstr {
  override def render(): String = s"${result.render()} = load ${result.tp.render()}, ${ptr.renderWithType()}"
}

case class IrCall(result: Option[IrVar], callee: IrValue, params: List[IrValue]) extends IrInstr {

  override def render(): String = {
    val fnType = callee.tp match {
      case IrPtrType(f: IrFunType) => f
      case f: IrFunType => f
      case IrPtrType(IrPtrType(f: IrFunType)) => f
      case other => throw new IllegalArgumentException(s"Cannot call non-function type: $other")
    }
    s"""${result.map(r => s"${r.render()} = ").getOrElse("")}call ${
      fnType.ret.render()
    } ${
      callee.render()
    }(${params.map(_.renderWithType()).mkString(", ")})"""
  }
}

sealed trait IrType {
  def render(): String
}

case class IrIntType(bits: Int) extends IrType {
  override def render(): String = s"i$bits"
}

object IrIntType {
  val I64 = IrIntType(64)
  val I32 = IrIntType(32)
  val I1 = IrIntType(1)
}
case class IrFloat64() extends IrType {
  override def render(): String = "double"
}
case class IrPtrType(to: IrType) extends IrType {
  override def render(): String = "ptr"
}

case class IrFunType(ret: IrType, params: List[IrType]) extends IrType {
  override def render(): String = "ptr"
}

object IrVoidType extends IrType {
  override def render(): String = "void"
}

object IrUnknownType extends IrType {
  override def render(): String = "???"
}

case class IrStructNamed(name: String) extends IrType {
  override def render(): String = s"%${name}"
}

case class IrStructTyped(name: String, fields: List[IrType]) extends IrType {
  override def render(): String = s"{ ${fields.map { f => f.render() }.mkString(", ")} }"
}

object IrVariadicType extends IrType {
  override def render(): String = "..."
}

sealed trait IrValue {
  def render(): String

  def tp: IrType

  def renderWithType(): String = s"${tp.render()} ${render()}"
}

sealed trait IrSSAValue extends IrValue

case class IrVar(override val tp: IrType, name: String) extends IrSSAValue {
  override def render(): String = s"%$name"
}

object IrNullValue extends IrValue {

  override def render(): String = "null"
  override def tp: IrType = IrPtrType(IrUnknownType)
}

sealed trait IrConstant extends IrValue

sealed trait IrGlobalValue extends IrConstant {
  def renderGlobal(): String
}


// const char* with fixed size
case class IrConstChar(size: Int) extends IrType {

  //+1 to account for \0
  override def render(): String = s"[${size+1} x i8]"
}

case class IrFunctionRef(fun: IrFunctionLike) extends IrGlobalValue {

  override def tp = fun.signature

  override def render() = s"@${fun.name}"

  override def renderGlobal(): String = render()

  def this(irDeclFun: IrDeclFun)= {
    this(IrFun(irDeclFun.name, IrFunType(irDeclFun.signature.ret, irDeclFun.signature.params), null, null))
  }
}

case class IrConst(override val tp: IrType, value: Any) extends IrConstant {
  override def render(): String = s"$value"
}

object IrConst {
  def apply(value: Long) = new IrConst(IrIntType.I64, value)

  def apply(value: Boolean) = new IrConst(IrIntType.I1, if (value) 1 else 0)

  def apply(value: Double) = new IrConst(IrFloat64(), value)

  //def apply(value: String) = new IrConst(IrConstChar, value)
}

/*
  name: Name of the builtin in UPL
  retType: return type of the builtin Method
  param: expected parameters of the builtin Method
 */
abstract class IrBuiltin(val name: String, val retType: IrType, val param: List[IrType]) {
  def llvmName: String = s"Builtin.$name"
  def generateFunction(): (IrDeclFun, IrFun)
}
case class IrSimpleBuiltin(override val name: String, override val retType: IrType, override val param: List[IrType],
                           llvmBuiltin: String) extends IrBuiltin(name, retType, param) {

  override def generateFunction(): (IrDeclFun, IrFun) = {
    val decl = IrDeclFun(llvmBuiltin, IrFunType(retType, param))
    var i = 0
    val params = param.map(x => {
      val arg = IrVar(x, s"param$i")
      i = i +1
      arg
    })

    val ret = IrVar(retType, "res")
    val call = IrCall(Some(ret), new IrFunctionRef(decl), params)

    val fun = IrFun(llvmName, IrFunType(retType, param), params,
      List(IrBlock("builtin", List(call, IrReturn(ret)))))

    (decl, fun)
  }
}

case class IrBuiltinRead()
  extends IrBuiltin("read", IrConstChar(0), null) {

  override def generateFunction(): (IrDeclFun, IrFun) = {
    val decl = IrDeclFun("getline", IrFunType(IrIntType.I64, List(IrPtrType(IrConstChar(0)),
      IrPtrType(IrIntType.I64), IrPtrType(IrIntType.I64))))

    val cPtr = IrAlloca(IrVar(IrPtrType(null), "line"))
    val size = IrAlloca(IrVar(IrPtrType(null), "size"))
    val s1 = IrStore(IrNullValue, cPtr.result)
    val s2 = IrStore(IrConst(IrIntType.I64, 0), size.result)
    val stdin = IrVar(IrPtrType(IrPtrType(null)), "stdin")
    val l1 = IrLoad(stdin, SpecialFunctions.stdin)
    val call = IrCall(None, new IrFunctionRef(decl), List(cPtr.result, size.result, stdin))
    val res = IrVar(IrPtrType(null), "res")
    val l2 = IrLoad(res, cPtr.result)
    val fun = IrFun(llvmName, IrFunType(IrPtrType(null), List(IrVoidType)), List.empty,
      List(IrBlock("builtin", List(cPtr, size, s1, s2, l1, call, l2, IrReturn(res)))))

    (decl, fun)
  }
}



object builtins {
  var Builtins: Seq[IrBuiltin] = Seq(
    IrSimpleBuiltin("print", IrIntType.I32, List[IrType](IrPtrType(IrConstChar(0))), "puts"),
    IrSimpleBuiltin("sin",IrFloat64(), List[IrType]{IrFloat64()}, "llvm.sin.f64"),
    IrBuiltinRead()
  )
}

object rationalNumbers {
  val decl = IrStruct("Uniformal.Rat", List(IrIntType.I64, IrIntType.I64))

  def add(): (IrDeclFun, IrFun) = {

    val declAdd = IrDeclFun("Uniformal.Rat.Add", IrFunType(IrStructTyped(decl.name, decl.fields), List(IrPtrType(decl), IrPtrType(decl))))

    val lhsPar = IrVar(IrPtrType(null), "param1")
    val rhsPar = IrVar(IrPtrType(null), "param2")
    val ret = IrVar(IrStructNamed(decl.name), "res")

    val res = IrAlloca(ret)
    val lhsVal = IrVar(IrPtrType(null), "lhsAddr")
    val rhsVal = IrVar(IrPtrType(null), "rhsAddr")

    val tmp0 = IrVar(IrPtrType(null), "0")
    IrLoad(tmp0, lhsVal)
    val enu = IrVar(IrPtrType(null), "enu")
    val tmp1 = IrVar(IrIntType.I64, "1")
    val tmp2 = IrVar(IrPtrType(null), "2")

    val deno = IrVar(IrPtrType(null), "deno")
    val tmp3 = IrVar(IrIntType.I64, "3")
    val mul = IrVar(IrIntType.I64, "mul")
    val mul3 = IrVar(IrIntType.I64, "mul3")
    val mul7 = IrVar(IrIntType.I64, "mul7")
    val addV = IrVar(IrIntType.I64, "add")

    val enu1 = IrVar(IrPtrType(null), "enu1")
    val enu4 = IrVar(IrPtrType(null), "enu4")
    val tmp4 = IrVar(IrPtrType(null), "4")
    val deno2 = IrVar(IrPtrType(null), "deno2")
    val deno6 = IrVar(IrIntType.I64, "deno6")
    val deno8 = IrVar(IrIntType.I64, "deno8")

    val tmp5 = IrVar(IrIntType.I64, "5")
    val tmp6 = IrVar(IrPtrType(null), "6")
    val tmp7 = IrVar(IrIntType.I64, "7")
    val tmp9 = IrVar(IrIntType.I64, "9")
    val tmp10 = IrVar(IrPtrType(null), "10")
    val tmp11 = IrVar(IrIntType.I64, "11")

    val tmp8 = IrVar(IrPtrType(null), "8")
    val tmp12 = IrVar(IrStructTyped("", List(IrIntType.I64, IrIntType.I64)), "12")
    val deno5 = IrVar(IrIntType.I64, "deno5")

    val instr = IrBlock("entry", List(res, IrAlloca(lhsVal), IrAlloca(rhsVal), IrStore(lhsPar, lhsVal), IrStore(rhsPar, rhsVal), IrLoad(tmp0, lhsVal),
      IrGetElement(enu, decl, tmp0, List(0,0)), IrLoad(tmp1, enu), IrLoad(tmp2, lhsVal), IrGetElement(deno, decl, tmp2, List(0, 1)),
      IrLoad(tmp3, deno), IrBinOp(mul, IMUL, tmp1, tmp3), IrLoad(tmp4, rhsVal), IrGetElement(enu1, decl, tmp4, List(0, 0)), IrLoad(tmp5, enu1), IrLoad(tmp6, lhsVal), IrGetElement(deno2, decl, tmp6, List(0,1)),
      IrLoad(tmp7, deno2), IrBinOp(mul3, IMUL, tmp5, tmp7), IrBinOp(addV, Operation.IADD, mul, mul3), IrGetElement(enu4, decl, ret, List(0,0)), IrStore(addV, enu4), IrLoad(tmp8, lhsVal), IrGetElement(deno5, decl, tmp8, List(0,1)), IrLoad(tmp9, deno5),
      IrLoad(tmp10, rhsVal), IrGetElement(deno6, decl, tmp10, List(0,1)), IrLoad(tmp11, deno6), IrBinOp(mul7, IMUL,tmp9, tmp11), IrGetElement(deno8, decl, ret, List(0,1)), IrStore(mul7, deno8), IrLoad(tmp12, IrVar(IrPtrType(null), "res")), IrReturn(tmp12)
    ))
    val fun = IrFun("Uniformal.Rat.Add", declAdd.signature, List(lhsPar, rhsPar), List(instr))
    (declAdd, fun)
  }

  def mul(): (IrDeclFun, IrFun) = {
    val declMul = IrDeclFun("Uniformal.Rat.mul", IrFunType(IrStructTyped(decl.name, decl.fields), List(IrPtrType(decl), IrPtrType(decl))))

    val lhsPar = IrVar(IrPtrType(null), "param1")
    val rhsPar = IrVar(IrPtrType(null), "param2")
    val ret = IrVar(IrStructNamed(decl.name), "res")

    val res = IrAlloca(ret)
    val lhsVal = IrVar(IrPtrType(null), "lhsAddr")
    val rhsVal = IrVar(IrPtrType(null), "rhsAddr")

    val tmp0 = IrVar(IrPtrType(null), "0")
    IrLoad(tmp0, lhsVal)
    val enu = IrVar(IrPtrType(null), "enu")
    val tmp1 = IrVar(IrIntType.I64, "1")
    val tmp2 = IrVar(IrPtrType(null), "2")

    val deno = IrVar(IrPtrType(null), "deno")
    val tmp3 = IrVar(IrIntType.I64, "3")
    val mul = IrVar(IrIntType.I64, "mul")

    val enu1 = IrVar(IrPtrType(null), "enu1")
    val tmp4 = IrVar(IrPtrType(null), "4")
    val enu2 = IrVar(IrPtrType(null), "enu2")

    val tmp5 = IrVar(IrIntType.I64, "5")
    val tmp6 = IrVar(IrPtrType(null), "6")
    val tmp7 = IrVar(IrIntType.I64, "7")
    val tmp8 = IrVar(IrStructTyped("", List(IrIntType.I64, IrIntType.I64)), "8")
    val mul4 = IrVar(IrPtrType(null), "mul4")
    val deno3 = IrVar(IrPtrType(null), "deno2")
    val deno5 = IrVar(IrIntType.I64, "deno5")

    val instr = IrBlock("entry", List(res, IrAlloca(lhsVal), IrAlloca(rhsVal), IrStore(lhsPar, lhsVal), IrStore(rhsPar, rhsVal), IrLoad(tmp0, lhsVal),
      IrGetElement(enu, decl, tmp0, List(0,0)), IrLoad(tmp1, enu), IrLoad(tmp2, rhsVal), IrGetElement(enu1, decl, tmp2, List(0, 0)),
      IrLoad(tmp3, enu1), IrBinOp(mul, IMUL, tmp1, tmp3), IrGetElement(enu2, decl, ret, List(0,0)), IrStore(mul, enu2),
      IrLoad(tmp4, lhsVal), IrGetElement(deno, decl, tmp4, List(0, 1)), IrLoad(tmp5, deno), IrLoad(tmp6, rhsVal),
      IrGetElement(deno3, decl, tmp6, List(0, 1)), IrLoad(tmp7, deno3), IrBinOp(mul4, IMUL, tmp5, tmp7), IrGetElement(deno5, decl, ret, List(0, 1)),
      IrStore(mul4, deno5), IrLoad(tmp8, IrVar(IrPtrType(null), "res")), IrReturn(tmp8)
    ))

    val fun = IrFun("Uniformal.Rat.Mul", declMul.signature, List(lhsPar, rhsPar), List(instr))
    (declMul, fun)
  }

  def negate(): (IrDeclFun, IrFun) = {
    val declNegate = IrDeclFun("Uniformal.Rat.negate", IrFunType(IrStructTyped(decl.name, decl.fields), List(IrPtrType(decl))))

    val lhsPar = IrVar(IrPtrType(null), "param1")
    val ret = IrVar(IrStructNamed(decl.name), "res")

    val res = IrAlloca(ret)
    val lhsVal = IrVar(IrPtrType(null), "lhsAddr")

    val tmp0 = IrVar(IrPtrType(null), "0")
    val enu = IrVar(IrPtrType(null), "enu")
    val tmp1 = IrVar(IrIntType.I64, "1")
    val tmp2 = IrVar(IrPtrType(null), "2")

    val deno = IrVar(IrPtrType(null), "deno")
    val tmp3 = IrVar(IrIntType.I64, "3")
    val sub = IrVar(IrIntType.I64, "sub")

    val enu1 = IrVar(IrPtrType(null), "enu1")
    val tmp8 = IrVar(IrStructTyped("", List(IrIntType.I64, IrIntType.I64)), "8")
    val deno2 = IrVar(IrIntType.I64, "deno2")

    val instr = IrBlock("entry", List(res, IrAlloca(lhsVal), IrStore(lhsPar, lhsVal), IrGetElement(enu, decl, ret, List(0,0)),
      IrLoad(tmp0, lhsVal), IrGetElement(enu1, decl, tmp0, List(0, 0)),
      IrLoad(tmp1, enu1), IrBinOp(sub, ISUB, IrConst(0), tmp1),
      IrStore(sub, enu), IrGetElement(deno, decl, ret, List(0, 1)), IrLoad(tmp2, lhsVal), IrGetElement(deno2, decl, tmp2, List(0,1)),
      IrLoad(tmp3, deno2), IrStore(tmp3, deno), IrLoad(tmp8, IrVar(IrPtrType(null), "res")), IrReturn(tmp8)
    ))
    val fun = IrFun("Uniformal.Rat.Negate", declNegate.signature, List(lhsPar), List(instr))
    (declNegate, fun)
  }

  def invert(): (IrDeclFun, IrFun) = {
    val declInvert = IrDeclFun("Uniformal.Rat.invert", IrFunType(IrStructTyped(decl.name, decl.fields), List(IrPtrType(decl))))

    val lhsPar = IrVar(IrPtrType(null), "param1")
    val ret = IrVar(IrStructNamed(decl.name), "res")

    val res = IrAlloca(ret)
    val lhsVal = IrVar(IrPtrType(null), "lhsAddr")

    val tmp0 = IrVar(IrPtrType(null), "0")
    val enu = IrVar(IrPtrType(null), "enu")
    val tmp1 = IrVar(IrIntType.I64, "1")
    val tmp2 = IrVar(IrPtrType(null), "2")

    val deno = IrVar(IrPtrType(null), "deno")
    val tmp3 = IrVar(IrIntType.I64, "3")

    val enu2 = IrVar(IrPtrType(null), "enu2")
    val tmp8 = IrVar(IrStructTyped("", List(IrIntType.I64, IrIntType.I64)), "8")
    val deno1 = IrVar(IrIntType.I64, "deno1")

    val instr = IrBlock("entry", List(res, IrAlloca(lhsVal), IrStore(lhsPar, lhsVal), IrGetElement(enu, decl, ret, List(0,0)),
      IrLoad(tmp0, lhsVal), IrGetElement(deno, decl, tmp0, List(0, 1)),
      IrLoad(tmp1, deno),
      IrStore(tmp1, enu), IrGetElement(deno1, decl, ret, List(0, 1)), IrLoad(tmp2, lhsVal), IrGetElement(enu2, decl, tmp2, List(0,0)),
      IrLoad(tmp3, enu2), IrStore(tmp3, deno1), IrLoad(tmp8, IrVar(IrPtrType(null), "res")), IrReturn(tmp8)
    ))
    val fun = IrFun("Uniformal.Rat.Invert", declInvert.signature, List(lhsPar), List(instr))
    (declInvert, fun)
  }
}

case class IrRational(enu: Long, deno: Long, initLabel: String) extends IrValue {
  override def render(): String = rationalNumbers.decl.render()
  override def tp: IrType = rationalNumbers.decl
}