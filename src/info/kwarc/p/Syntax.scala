package info.kwarc.p

case class Location(file: File, from: Int, to: Int) {
  override def toString = file.getName + s"#$from:$to"
}

sealed abstract class SyntaxFragment {
  private[p] var loc: Location = null // set by parser to remember location in source
  private[p] var redundant = false // can be used to mark to be removed later, e.g., when declarations are subsumed
  /** moves over mutable fields, may be called after performing traversals
    * if the resulting expression is "the same" as the original in some sense
    * if needed, it is usually to implement the traversal using also SyntaxFragment.matchC in the first place
    */
  def copyFrom(sf: SyntaxFragment): this.type = {
    loc = sf.loc
    redundant = sf.redundant
    this
  }
}
object SyntaxFragment {
  /** applies a function, usually by case-matching, and copies mutable data over (see copyFrom) */
  def matchC[A<:SyntaxFragment](a: A)(f: A => A): A = {
    f(a).copyFrom(a)
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
  def decls: List[A]
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
  val empty = Path(Nil)
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
    val (before,_ :: after) = decls.splitAt(decls.indexOf(old))
    nw.copyFrom(old)
    before ::: nw :: after
  }
}

sealed trait NestingDeclaration[A <: Declaration] extends Declaration with HasChildren[Declaration] {
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
  def lookupModule(path: Path): Option[Module] = lookupPath(path) match {
    case s@Some(m: Module) => Some(m)
    case _ => None
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

sealed abstract class ExpressionOrType extends SyntaxFragment

sealed trait AtomicDeclaration extends Declaration {
  def tp: Type
  val dfO: Option[ExpressionOrType]
}

case class Vocabulary(decls: List[Declaration]) extends UnnamedDeclaration with NestingDeclaration[Vocabulary] {
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

case class Inclusion(path: Path, dfO: Option[Expression]) {
  private[p] var redundant = false
  def compose(that: Inclusion) = that.dfO match {
    case None => this
    case Some(andThen) => dfO match {
      case None => copy(dfO = that.dfO)
      case Some(df) =>
        val dfC = OwnerSubstitutor(andThen,df)
        copy(dfO = Some(dfC))
    }
  }
}
object Inclusion {
  def apply(p: Path): Inclusion = Inclusion(p, None)
}

case class Theory(parts: List[Inclusion]) extends SyntaxFragment {
  override def toString = parts.mkString(" + ")
  private[p] var isFlat = false
  override def copyFrom(sf: SyntaxFragment): this.type = {
    super.copyFrom(sf)
    sf match {
      case t: Theory => isFlat = t.isFlat
      case _ =>
    }
    this
  }
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
  def apply(p: Path): Theory = Theory(List(Inclusion(p)))
}

case class StaticEnvironment(voc: Vocabulary, parent: Path, scopes: List[(Theory,Context)]) {
  def push(t: Theory) = copy(scopes = (t,Context.empty)::scopes)
  def pop() = copy(scopes = scopes.tail)
  def theory = scopes.head._1
  def ctx = scopes.head._2
  def add(c: Context): StaticEnvironment = copy(scopes = (theory, ctx.append(c))::scopes)
  def add(vd: VarDecl): StaticEnvironment = add(Context(List(vd)))
  def update(p: Path, old: Declaration, nw: Declaration) = {
    if (old == nw) this else {
      copy(voc = voc.update(p,old,nw))
    }
  }
  def enter(n: String) = copy(parent = parent/n)
  def leave = copy(parent = parent.up())
  def parentDecl = voc.lookupPath(parent)
}
object StaticEnvironment {
  def apply(p: Program): StaticEnvironment = StaticEnvironment(p.voc, Path(Nil), List((Theory.empty, Context.empty)))
}

// ***************** Programs **************************************
case class Program(voc: Vocabulary, main: Expression) extends SyntaxFragment {
  override def toString = voc + "\n" + main
}

case class Module(name: String, closed: Boolean, decls: List[Declaration]) extends NamedDeclaration with NestingDeclaration[Module] {
  override def toString = {
    val k = if (closed) "class" else "module"
    s"$k $name {\n${decls.mkString("\n").indent(2)}}"
  }
  def update(old: Declaration, nw: Declaration) = {
    val mC = copy(decls = Declaration.update(decls, old, nw))
    mC.supers = supers
    mC
  }
  // filled during type-checking
  /** parent theory */
  private[p] var supers: Theory = null
  /** flat set of undefined fields that instances must define */
  private[p] var flat: List[SymbolDeclaration] = null
  private[p] def abstractFields = flat.collect {case sd if sd.dfO.isEmpty => sd.name}
  /** realized parents */
  private[p] var realizes: List[Path] = null
  /** if thisPath is the path to this module, this module as a theory */
  private[p] def theory(thisPath: Path) = Theory(Inclusion(thisPath)::supers.parts)
  override def copyFrom(sf: SyntaxFragment) = {
    super.copyFrom(sf)
    sf match {
      case m: Module =>
        supers = m.supers
        flat = m.flat
        realizes = m.realizes
      case _ =>
    }
    this
  }
}

sealed trait SymbolDeclaration extends NamedDeclaration with AtomicDeclaration {
  def kind: String // expression, type, ...
  override def toString = {
    val tpS = if (tp == null || tp == AnyType) "" else " <  " + tp.toString
    val dfOS = dfO match {case Some(t) => " = " + t case None => ""}
    kind + name+tpS+dfOS
  }
}

case class ExprDecl(name: String, tp: Type, dfO: Option[Expression]) extends SymbolDeclaration {
  def kind = "val"
}

case class TypeDecl(name: String, tp: Type, dfO: Option[Type]) extends SymbolDeclaration {
  def kind = "type"
}

case class Include(dom: Theory, dfO: Option[Expression]) extends UnnamedDeclaration with AtomicDeclaration {
  def tp = ClassType(dom)
  override def toString = {
    val kw = if (realize) "realize" else "include"
    val dfS = dfO match {case None | Some(null) => "" case Some(d) => " = " + d.toString}
    kw + " " + dom + dfS
  }
  // we use Some(null) to track which includes must be fully defined when the containing module ends
  def realize = dfO contains null
}
object Include {
  def apply(p: Path, realize: Boolean = false): Include = Include(Theory(p), if (realize) Some(null) else None)
}

// case class Foreign(format: String, parts: List[(String, SyntaxFragment)], lastPart: String) extends UnnamedDeclaration

// ***************** Types **************************************
sealed abstract class Type extends ExpressionOrType

case class TypeRef(path: Path) extends Type {
  override def toString = path.toString
}

/* Defined types are known from the outside and normalize to their definiens.
 * Undefined types are abstract from the outside even after defining them during instance creation.
 * Accessing them requires a pure owner and returns an unknown type.
 * The only way to create values for it is by calling methods on an instance that is
 * statically known to be equal when restricted to the class declaring the type field.
 */
// checker must ensure owner is Pure (Scala path types: owner must be variable to separate side effects from type field access.)
// instance creation and field references must take type fields into account
// interpreter invariant: semantics should not depend on types other than class refs, computation of types should never be needed,
// i.e., removing all types from declarations and type fields from modules/instances should be allowed
case class TypeFieldRef(owner: Option[Expression], name: String) extends Type {
  override def toString = {
    val ownerS = owner match {
      case None => ""
      case Some(e) => e + "."
    }
    ownerS+name
  }
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
case class OptionType(elem: Type) extends TypeOperator(List(elem)) {
  override def toString = s"Option[$elem]"
}

// ***************** Expressions **************************************
sealed abstract class Expression extends ExpressionOrType

case class SymbolRef(path: Path) extends Expression {
  override def toString = path.toString
}

case class Instance(theory: Theory, decls: List[AtomicDeclaration]) extends Expression with HasChildren[Declaration] with MutableExpressionStore {
  // non-null exactly for run-time instances
  private[p] var fields: List[MutableExpression] = null
  def isRuntime = fields != null
  override def equals(that: Any): Boolean = {
    that match {
      case that: Instance =>
        if (fields != null) {
          this eq that
        }
        else {
          this.theory == that.theory && this.decls == that.decls
        }
      case _ => false
    }
  }
  override def copyFrom(sf: SyntaxFragment): this.type = {
    super.copyFrom(sf)
    sf match {
      case i: Instance => fields = i.fields
      case _ =>
    }
    this
  }
}

case class FieldRef(owner: Option[Expression], name: String) extends Expression {
  override def toString = {
    val ownerS = owner match {
      case None => ""
      case Some(e) => e + "."
    }
    ownerS+name
  }
}

case class InstanceWith(exp: Expression, tp: Path) extends Expression {
  override def toString = exp + "#" + tp
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
  // used at run-time to store the frame relative to which the body must be interpreted when the function is applied
  private[p] var frame: Frame = null
  override def copyFrom(sf: SyntaxFragment): this.type = {
    super.copyFrom(sf)
    sf match {
      case l: Lambda => frame = l.frame
      case _ =>
    }
    this
  }

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