package info.kwarc.p.compiler

case class IrProgram(declaredFunctions: List[IrDeclFun], structs: List[IrStruct], globals: List[IrGlobal],
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

case class IrFun(name: String, signature: IrFunType, params: List[IrArgument], blocks: List[IrBlock]) extends
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

case class IrPhi(result: IrValue, values: List[(IrValue, String)]) extends IrInstr {
  override def render() = s"${result.render()} = phi ${
    result.tp.render()
  } ${values.map(v => s"[ ${v._1.render()}, %${v._2} ]").mkString(", ")}"
}

case class IrGetElement(result: IrVar, struct: IrStruct, ptr: IrValue, vals: List[Int]) extends IrInstr {
  override def render(): String = s"${result.render()} = getelementptr ${struct.render()}, ${
    ptr.renderWithType()
  }, ${vals.map(v => s"i32 $v").mkString(", ")}"
}

case class IrComputeSize(result: IrVar, struct: IrStruct) extends IrInstr {
  override def render(): String = s"${result.render()} = ptrtoint ${struct.render()}* getelementptr (${
    struct.render()
  }, ${struct.render()}* null, i32 1) to ${result.tp.render()}"
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
  val I1 = IrIntType(1)
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

sealed trait IrValue {
  def render(): String

  def tp: IrType

  def renderWithType(): String = s"${tp.render()} ${render()}"
}

sealed trait IrSSAValue extends IrValue

case class IrVar(override val tp: IrType, name: String) extends IrSSAValue {
  override def render(): String = s"%$name"
}

case class IrArgument(tp: IrType, name: String) extends IrSSAValue {
  override def render(): String = s"%$name"
}

sealed trait IrConstant extends IrValue

sealed trait IrGlobalValue extends IrConstant

case class IrFunctionRef(fun: IrFunctionLike) extends IrGlobalValue {

  override def tp = IrPtrType(fun.signature)

  override def render() = s"@${fun.name}"
}

case class IrConst(override val tp: IrType, value: Long) extends IrConstant {
  override def render(): String = s"$value"
}

object IrConst {
  def apply(value: Long) = new IrConst(IrIntType.I64, value)

  def apply(value: Boolean) = new IrConst(IrIntType.I1, if (value) 1 else 0)
}
