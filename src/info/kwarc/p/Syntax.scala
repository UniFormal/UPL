package info.kwarc.p

case class Location(file: File, from: Int, to: Int) {
  override def toString = file.getName + s"#$from:$to"
}

sealed abstract class SyntaxFragment {
  private[p] var loc: Location = null
}
object SyntaxFragment {
  def keepRef[A<:SyntaxFragment](pre: A)(f: A => A): A = {
    val post = f(pre)
    post.loc = pre.loc
    pre
  }
}

abstract class PError(msg: String) extends Exception(msg)
case class IError(msg: String) extends PError(msg)

sealed trait MaybeNamed extends SyntaxFragment {
  def nameO: Option[String]
}

sealed trait Named extends MaybeNamed {
  def name: String
  def nameO: Some[String] = Some(name)
}

sealed trait HasChildren[A <: MaybeNamed] extends SyntaxFragment {
  val decls: List[A]
  def domain = decls collect {case d: Named => d.name}
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

object Path {
  import Character._
  val isCharClasses = List(CONNECTOR_PUNCTUATION)
  def isIdChar(c: Char) = c.isLetter || c.isDigit || isCharClasses.contains(c.getType)
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
    val (before,old :: after) = decls.splitAt(decls.indexOf(old))
    nw.loc = old.loc
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
    case hd::_ => lookupO(hd).flatMap {d => d.lookupPath(path.tail)}
  }
  // looks up par/p, par.up/p, par.up.up/p, ... , p and returns the first that exists
  def lookupRelativePath(par: Path, p: Path): Option[(Path, Declaration)] = {
    val pp = par/p
    lookupPath(pp) match {
      case Some(d) => Some((pp,d))
      case None =>
        if (par.isRoot)
          None
        else
          lookupRelativePath(par.up(),p)
    }
  }
  def lookupClass(path: Path, exc: PError): Module = lookupPath(path) match {
    case Some(m: Module) => m
    case _ => throw exc
  }

  def update(old: Declaration, nw: Declaration): A
  def update(p: Path, old: Declaration, nw: Declaration): A = {
    if (p.isRoot) {
      update(old,nw)
    } else {
      val parent = lookup(p.head)
      parent match {
        case mod: Module =>
          val parentU = mod.update(p.tail,old,nw)
          update(parent,parentU)
        case _ => throw IError("not nestable")
      }
    }
  }
}

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

case class Theory(parts: List[Path]) {
  override def toString = parts.mkString(" + ")
  private[p] var isFlat = false
  override def equals(that: Any) = that match {
    case Theory(those) =>
      // hardcode commutativity, idempotency of union
      parts.length == those.length && (parts intersect those) == parts
    case _ => false
  }
  override def hashCode(): Int = parts.sortBy(_.toString).hashCode()
}
object Theory {
  def empty = Theory(Nil)
}

case class StaticEnvironment(voc: Vocabulary, parent: Path, scopes: List[(Theory,Context)]) {
  def push(t: Theory) = copy(scopes = (t,Context.empty)::scopes)
  def pop() = copy(scopes = scopes.tail)
  def theory = scopes.head._1
  def ctx = scopes.head._2
  def add(c: Context) = copy(scopes = (theory, ctx.append(c))::scopes)
  def add(vd: VarDecl) = add(Context(List(vd)))
  def update(p: Path, old: Declaration, nw: Declaration) = {
    if (old == nw) this else {
      copy(voc = voc.update(p,old,nw))
    }
  }
  def enter(n: String) = copy(parent = parent/n)
  def leave = copy(parent = parent.up())
}
object StaticEnvironment {
  def apply(p: Program): StaticEnvironment = StaticEnvironment(p.voc, Path(Nil), List((Theory.empty, Context.empty)))
}

// ***************** Programs **************************************
case class Program(voc: Vocabulary, main: Expression) extends SyntaxFragment {
  override def toString = voc + "\n" + main
}

trait HasDefiniens[A<:SyntaxFragment] {
  val dfO: Option[A]
}

case class Module(name: String, open: Boolean, decls: List[Declaration]) extends NamedDeclaration with HasDeclarations[Module] {
  override def toString = {
    val k = if (open) "module" else "class"
    s"$k $name {\n${decls.mkString("\n").indent(2)}}"
  }
  private[p] var supers: List[Path] = null
  def update(old: Declaration, nw: Declaration) = {
    copy(decls = Declaration.update(decls, old, nw))
  }
}

case class SymDecl(name: String, tp: Type, dfO: Option[Expression]) extends NamedDeclaration with HasDefiniens[Expression] {
  override def toString = {
    val tpS = if (tp == null) "???" else tp.toString
    val dfS = dfO match {case Some(d) => " = " + d case None => ""}
    s"$name: $tpS$dfS"
  }
}

case class TypeDecl(name: String, dfO: Option[Type]) extends NamedDeclaration with HasDefiniens[Type] {
  override def toString = {
    val dfOS = dfO match {case Some(t) => " = " + t case None => ""}
    "type " + name+dfOS
  }
}

case class Include(dom: Theory, dfO: Option[Expression], realize: Boolean) extends UnnamedDeclaration with HasDefiniens[Expression] {
  override def toString = {
    val kw = if (realize) "realize" else "include"
    val dfS = dfO match {case None => "" case Some(d) => " = " + d.toString}
    kw + " " + dom + dfS
  }
}

case class Foreign(format: String, parts: List[(String, SyntaxFragment)], lastPart: String) extends UnnamedDeclaration


// ***************** Types **************************************
sealed abstract class Type extends SyntaxFragment

case class TypeRef(path: Path) extends Type {
  override def toString = path.toString
}

case class ClassType(domain: Theory) extends Type {
  override def toString = "|" + domain.toString + "|"
}

/** the type of instances of any class */
object AnyStructure {
  def apply() = ClassType(Theory(Nil))
  def unapply(t: Type) = t match {
    case ClassType(Theory(Nil)) => Some(())
    case _ =>
  }
}

case class StructureType(decls: List[Declaration]) extends Type {
  override def toString = decls.mkString("{", ",", "}")
}

case class ExprsOver(scope: Theory, tp: Type) extends Type {
  override def toString = s"<$scope>$tp"
}

sealed abstract class BaseType(name: String) extends Type {
  override def toString = name
}
case object EmptyType extends BaseType("empty")
case object UnitType extends BaseType("unit")
case object BoolType extends BaseType("bool")
case object IntType extends BaseType("int")
case object RatType extends BaseType("rat")
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

// ***************** Expressions **************************************
sealed abstract class Expression extends SyntaxFragment {
  protected[p] var interpreted = false
}

case class SymbolRef(path: Path) extends Expression {
  override def toString = path.toString
}

case class Structure(decls: List[Declaration]) extends Expression with HasChildren[Declaration]

case class FieldRef(owner: Expression, name: String) extends Expression {
  override def toString = s"$owner.$name"
}
case class VarRef(name: String) extends Expression {
  override def toString = name
}

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

case class ExprOver(scope: Theory, expr: Expression) extends Expression {
  override def toString = s"<{$scope} $expr>"
}
case class Eval(syntax: Expression) extends Expression {
  override def toString = s"`$syntax`"
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

case class Lambda(ins: Context, body: Expression) extends Expression {
  // used during interpretation to store the frame relative to which the body must be interpreted when the function is applied
  private[p] var frame: Frame = null
  override def toString = s"($ins) -> $body"
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

sealed abstract class BaseValue(val value: Any, val tp: BaseType) extends Expression
case object UnitValue extends BaseValue((), UnitType) {
  override def toString = "()"
}
case class BoolValue(v: Boolean) extends BaseValue(v, BoolType) {
  override def toString = value.toString
}
case class IntValue(v: Int) extends BaseValue(v, IntType) {
  override def toString = value.toString
}
case class RatValue(enum: Int, denom: Int) extends BaseValue(enum/denom, RatType) {
  override def toString = enum.toString + "/" + denom.toString
}
object IntOrRatValue {
  def apply(e:Int, d: Int): BaseValue = {
    val g = 1 // gcd(e,d)
    val eg = e/g
    val dg = d/g
    if (dg == 1) IntValue(e) else RatValue(eg,dg)
  }
  def unapply(e: Expression) = e match {
    case IntValue(i) => Some((i,1))
    case RatValue(i,j) => Some((i,j))
    case _ => None
  }
}
case class StringValue(v: String) extends BaseValue(v, StringType) {
  override def toString = "\"" + String.escape(v) + "\""
}
object String {
  def escape(s:String) = s.replace("\\", "\\\\").replace("\"","\\\"")
}

case class BaseOperator(operator: Operator, tp: Type) extends Expression

sealed abstract class Operator(val symbol: String)
sealed abstract class InfixOperator(s: String, val precedence: Int, val flexary: Boolean) extends Operator(s)
sealed abstract class PrefixOperator(s: String) extends Operator(s)

trait Arithmetic
trait Connective
trait Comparison
trait Equality

case object Plus extends InfixOperator("+", 0, false) with Arithmetic
case object Minus extends InfixOperator("-", 0, false) with Arithmetic
case object Times extends InfixOperator("*", 10, true) with Arithmetic
case object Divide extends InfixOperator("/", 10, false) with Arithmetic
case object Power extends InfixOperator("^", 20, false)
case object And extends InfixOperator("&", -20, true) with Connective
case object Or extends InfixOperator("|", -20, true) with Connective

case object Less extends InfixOperator("<", -10, false) with Comparison
case object LessEq extends InfixOperator("<=", -10, false) with Comparison
case object Greater extends InfixOperator(">", -10, false) with Comparison
case object GreaterEq extends InfixOperator(">=", -10, false) with Comparison
case object Equal extends InfixOperator("==", -10, false) with Equality
case object Inequal extends InfixOperator("!=", -10, false) with Equality

case object UMinus extends PrefixOperator("-")
case object Not extends PrefixOperator("!")

object Operator {
  val infixes = List(Plus, Minus, Times, Divide, Power, And, Or, Equal, Inequal, Less, LessEq, Greater, GreaterEq)
  val prefixes = List(UMinus,Not)
}