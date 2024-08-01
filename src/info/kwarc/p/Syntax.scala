package info.kwarc.p

sealed abstract class SyntaxFragment

abstract class PError(msg: String) extends Exception(msg)
case class IError(msg: String) extends PError(msg)

trait MaybeNamed extends SyntaxFragment {
  def nameO: Option[String]
}

trait Named extends MaybeNamed {
  def name: String
  def nameO: Some[String] = Some(name)
}

trait HasChildren[A <: MaybeNamed] extends SyntaxFragment {
  val decls: List[A]
  val domain = decls collect {case d: Named => d.name}
  def lookupO(name: String) = decls.find(_.nameO.contains(name))
  def lookup(name: String) = lookupO(name).get
}

case class Path(names: List[String]) extends SyntaxFragment {
  override def toString = names.mkString(".")
  def head = names.head
  def tail = Path(names.tail)
  def /(n: String) = Path(names:::List(n))
  def /(p: Path) = Path(names:::p.names)
  def up() = Path(names.init)
  def isRoot = names.isEmpty
}

sealed abstract class Declaration extends SyntaxFragment with MaybeNamed {
  def lookupPath(p: Path) = if (p.isRoot) Some(this) else None
}
sealed abstract class NamedDeclaration extends Declaration with Named
sealed abstract class UnnamedDeclaration extends Declaration {
  val nameO = None
}

object Declaration {
  def update(decls: List[Declaration], old: Declaration, nw: Declaration) = {
    val (before,_ :: after) = decls.splitAt(decls.indexOf(old))
    before ::: nw :: after
  }
  def merge(d1: Declaration, d2: Declaration) = (d1,d2) match {
    case (SymDecl(n1, tp1, v1), SymDecl(n2, tp2, v2)) if n1 == n2 =>
      val tpM = if (tp2 == null) tp1
        else if (tp1 == null) tp2
        else if (tp1 == tp2) tp1
        else throw IError("not mergable")
      val vM = if (v1.isEmpty) v2
        else if (v2.isEmpty) v1
        else if (v1 == v2) v1
        else throw IError("not mergable")
      SymDecl(n1, tpM, vM)
    case ((TypeDecl(n1,v1)), TypeDecl(n2,v2)) if n1 == n2 =>
      val vM = if (v1.isEmpty) v2
      else if (v2.isEmpty) v1
      else if (v1 == v2) v1
      else throw IError("not mergable")
      TypeDecl(n1, vM)
    case _ => if (d1 == d2) d1 else throw IError("not mergable")
  }
}

trait HasDeclarations[A <: Declaration] extends Declaration with HasChildren[Declaration] {
  override def lookupPath(path: Path): Option[Declaration] = path.names match {
    case Nil => Some(this)
    case hd::tl => lookupO(hd).flatMap {d => d.lookupPath(path.tail)}
  }
  def lookupClass(path: Path, exc: PError): Class = lookupPath(path) match {
    case Some(c: Class) => c
    case _ => throw exc
  }

  def update(old: Declaration, nw: Declaration): A
  def update(p: Path, old: Declaration, nw: Declaration): A = {
    if (p.isRoot) {
      update(old,nw)
    } else {
      val parent = lookup(p.head)
      parent match {
        case nd: NestingDeclaration =>
          val parentU = nd.update(p.tail,old,nw)
          update(parent,parentU)
        case _ => throw IError("not nestable")
      }
    }
  }
}

sealed abstract class NestingDeclaration extends NamedDeclaration with HasDeclarations[NestingDeclaration]

case class Vocabulary(decls: List[Declaration]) extends UnnamedDeclaration with HasDeclarations[Vocabulary] {
  override def toString = decls.mkString("\n")
  def append(d: Declaration) = Vocabulary(decls ::: List(d))
  def update(old: Declaration, nw: Declaration): Vocabulary = {
    copy(decls = Declaration.update(decls, old, nw))
  }
}
case class Context(decls: List[VarDecl]) extends SyntaxFragment with HasChildren[VarDecl] {
  override def toString = decls.mkString(", ")
  def append(c: Context) = Context(decls ::: c.decls)
  def append(d: VarDecl) = Context(decls ::: List(d))
}
object Context {
  val empty = Context(Nil)
}

case class StaticEnvironment(voc: Vocabulary, ctx: Context, parent: Path) {
  def add(c: Context) = copy(ctx = ctx.append(c))
  def add(vd: VarDecl) = copy(ctx = ctx.append(vd))
  def update(p: Path, old: Declaration, nw: Declaration) = {
    if (old == nw) this else {
      copy(voc = voc.update(p,old,nw))
    }
  }
  def enter(n: String) = copy(parent = parent/n)
  def leave = copy(parent = parent.up)
  // looks up par/p, par.up/p, par.up.up/p, ... , p and returns the first that exists
  def lookupRelativePath(par: Path, p: Path): Option[(Path, Declaration)] = {
    val pp = par/p
    voc.lookupPath(pp) match {
      case Some(d) => Some((pp,d))
      case None =>
        if (par.isRoot)
          None
        else
          lookupRelativePath(par.up,p)
    }
  }
}
object StaticEnvironment {
  def apply(p: Program): StaticEnvironment = StaticEnvironment(p.voc, Context.empty, Path(Nil))
}

case class Program(voc: Vocabulary, main: Expression) extends SyntaxFragment {
  override def toString = voc + "\n" + main
}

case class Module(name: String, decls: List[Declaration]) extends NestingDeclaration {
  override def toString = s"module $name {\n${decls.mkString("\n").indent(2)}}"
  def update(old: Declaration, nw: Declaration) = {
    copy(decls = Declaration.update(decls, old, nw))
  }
}

case class SymDecl(name: String, tp: Type, value: Option[Expression]) extends NamedDeclaration {
  override def toString = {
    val tpS = if (tp == null) "???" else tp.toString
    val vlS = value match {case Some(v) => " = " + v case None => ""}
    s"$name: $tpS$vlS"
  }
}

case class Class(name: String, supers: List[Type], decls: List[Declaration]) extends NestingDeclaration {
  override def toString = {
    val supersS = if (supers.isEmpty) "" else ": " + supers.mkString(", ") + " "
    s"class $name $supersS{\n${decls.mkString("\n").indent(2)}}"
  }
  def update(old: Declaration, nw: Declaration) = {
    copy(decls = Declaration.update(decls, old, nw))
  }

}
case class TypeDecl(name: String, df: Option[Type]) extends NamedDeclaration {
  override def toString = {
    val dfS = df match {case Some(t) => " = " + t case None => ""}
    "type " + name+dfS
  }
}

case class TypeRef(path: Path) extends Type {
  override def toString = path.toString
}
case class ClassUnion(classes: List[Type]) extends Type {
  override def toString = classes.mkString(", ")
}

sealed abstract class Type extends SyntaxFragment
sealed abstract class BaseType(name: String) extends Type {
  override def toString = name
}
case object EmptyType extends BaseType("empty")
case object UnitType extends BaseType("unit")
case object BoolType extends BaseType("bool")
case object IntType extends BaseType("int")
case object StringType extends BaseType("string")
case object AnyType extends BaseType("any")

sealed abstract class TypeOperator(val children: List[Type]) extends Type
case class FunType(ins: List[Type], out: Type) extends TypeOperator(ins:::List(out)) {
  override def toString = ProdType(ins) + " -> " + out
}
case class ProdType(comps: List[Type]) extends TypeOperator(comps) {
  override def toString = comps.mkString("(",", ", ")")
}
case class ListType(elem: Type) extends TypeOperator(List(elem)) {
  override def toString = s"List[$elem]"
}

sealed abstract class Expression extends SyntaxFragment

case class SymbolRef(path: Path) extends Expression {
  override def toString = path.toString
}
case class FieldRef(owner: Expression, name: String) extends Expression {
  override def toString = s"$owner.$name"
}
case class VarRef(name: String) extends Expression {
  override def toString = name
}

case class Block(exprs: List[Expression]) extends Expression {
  override def toString = exprs.mkString("{", " ", "}")
}
case class IfThenElse(cond: Expression, thn: Expression, els: Option[Expression]) extends Expression {
  override def toString = {
    val elsS = els.map(e => " else " + e).getOrElse("")
    s"if $cond $thn$elsS"
  }
}
case class While(cond: Expression, body: Expression) extends Expression
case class For(name: String, range: Expression, body: Expression) extends Expression

case class VarDecl(name: String, tp: Type, value: Option[Expression], mutable: Boolean) extends Expression with Named {
  def defined = value.isDefined
  override def toString = {
    val tpS = if (tp == null) "???" else tp.toString
    val vlS = value match {case Some(v) => " = " + v.toString case None => ""}
    s"$name: $tpS$vlS"
  }
}
object VarDecl {
  def apply(n: String, tp: Type): VarDecl = VarDecl(n, tp, None, false)
}
case class Assign(target: Expression, value: Expression) extends Expression {
  override def toString = s"$target = $value"
}

case class Lambda(ins: Context, body: Expression) extends Expression {
  override def toString = s"($ins) -> body"
}
case class Application(fun: Expression, args: List[Expression]) extends Expression {
  override def toString = {
    fun match {
      case BaseOperator(o: InfixOperator,_) => args.mkString("("," " + o.symbol + " ",")")
      case BaseOperator(o: PrefixOperator,_) => o.symbol + args.mkString
      case _ => fun + args.mkString("(",", ",")")
    }
  }
}

case class Tuple(comps: List[Expression]) extends Expression {
  override def toString = comps.mkString("(", ", ", ")")
}
case class Projection(tuple: Expression, index: Int) extends Expression {
  override def toString = s"$tuple.$index"
}

case class ListValue(elems: List[Expression]) extends Expression {
  override def toString = s"List(${elems.mkString(",")})"
}
case class ListElem(list: Expression, position: Expression) extends Expression {
  override def toString = s"$list($position)"
}

sealed abstract class BaseValue(value: Any, val tp: BaseType) extends Expression {
  override def toString = value.toString
}
case object UnitValue extends BaseValue((), UnitType)
case class BoolValue(v: Boolean) extends BaseValue(v, BoolType)
case class IntValue(v: Int) extends BaseValue(v, IntType)
case class StringValue(v: String) extends BaseValue(v, StringType)

case class BaseOperator(operator: Operator, tp: Type) extends Expression

sealed abstract class Operator(val symbol: String)
sealed abstract class InfixOperator(s: String, val precedence: Int, val flexary: Boolean) extends Operator(s)
sealed abstract class PrefixOperator(s: String) extends Operator(s)

case object Plus extends InfixOperator("+", 0, true)
case object Minus extends InfixOperator("-", 0, false)
case object Times extends InfixOperator("*", 10, true)
case object Divide extends InfixOperator("/", 10, false)
case object Power extends InfixOperator("^", 20, false)
case object And extends InfixOperator("&", 10, true)
case object Or extends InfixOperator("|", 10, true)
case object Equal extends InfixOperator("==", -10, false)
case object Inequal extends InfixOperator("!=", -10, false)

case object Not extends PrefixOperator("!")

object Operator {
  val infixes = List(Plus, Minus, Times, Divide, Power, And, Or, Equal, Inequal)
  val prefixes = List(Not)
}