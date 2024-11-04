package info.kwarc.p

case class Location(file: File, from: Int, to: Int) {
  override def toString = file.getName + s"#$from:$to"
}


// ***************************** root classes and auxiliary data structures

/** parent of all errors */
abstract class PError(msg: String) extends Exception(msg)

/** implementation errors */
case class IError(msg: String) extends PError(msg)

/** parent of all classes in the AST */
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

/** identifiers */
case class Path(names: List[String]) extends SyntaxFragment {
  override def toString = names.mkString(".")
  def head = names.head
  def tail = Path(names.tail)
  def /(n: String) = Path(names:::List(n))
  def /(p: Path) = Path(names:::p.names)
  def up = Path(names.init)
  def isRoot = names.isEmpty
}

object Path {
  import Character._
  val empty = Path(Nil)
  val isCharClasses = List(CONNECTOR_PUNCTUATION)
  def isIdChar(c: Char) = c.isLetter || c.isDigit || isCharClasses.contains(c.getType)
}

/** parent of all anonymous objects like types, expressions, formulas, etc. */
sealed abstract class Object extends SyntaxFragment

/** types */
sealed trait Type extends Object {
  def known = true
  def skipUnknown = this
  def <--(ins:Type*) = FunType(ins.toList,this)
}
object Type {
  def unknown() = new UnknownType(null)
  val unbounded = AnyType
}

/** typed expressions */
sealed trait Expression extends Object {
  def field(f: String) = OwnedExpr(this, ClosedRef(f))
}

/** parent of all structuring classes like module, symbol declarations */
sealed abstract class Declaration extends SyntaxFragment with MaybeNamed
sealed abstract class NamedDeclaration extends Declaration with Named
sealed abstract class UnnamedDeclaration extends Declaration {
  val nameO = None
}

object Declaration {
  sealed abstract class Comparison
  case object Identical extends Comparison
  case object Independent extends Comparison
  case object Subsumes extends Comparison
  case object SubsumedBy extends Comparison
  case object Clashing extends Comparison

  def compare(d: Declaration, e: Declaration): Comparison = (d,e) match {
    case (Include(p1,d1,r1),Include(p2,d2,r2)) =>
      if (p1 != p2) {
        Independent
      } else {
        if (d1.isEmpty && d2.isEmpty) {
          // realize flags only matter if both includes are undefined
          if (r1 == r2) Identical
          else if (r1) Subsumes else SubsumedBy
        } else {
          compareOO(d1,d2)
        }
      }
    case (sd1: SymbolDeclaration,sd2: SymbolDeclaration) =>
      if (sd1.name != sd2.name) Independent
      else if (sd1.kind != sd2.kind) Clashing
      else if (sd1.tp == sd2.tp) compareOO(sd1.dfO,sd2.dfO)
      else Clashing // TODO: check subtyping, check equality, try to merge
    case _ => Independent
  }
  def compareOO(o1: Option[Object], o2: Option[Object]): Comparison = (o1,o2) match {
    case (Some(_),None) => Subsumes
    case (None,Some(_)) => SubsumedBy
    case (Some(x),Some(y)) => if (x == y) Identical else Clashing
    case (None,None) => Identical
  }
}

// ************************************* Contexts *****************************

/** object-level context: relative to a vocabulary and a choice of theory in it */
case class Context(decls: List[VarDecl]) extends SyntaxFragment with HasChildren[VarDecl] {
  override def toString = decls.mkString(", ")
  def append(c: Context): Context = copy(decls = decls ::: c.decls)
  def append(d: VarDecl): Context = append(Context(d))
}
object Context {
  val empty = Context(Nil)
  def apply(d: VarDecl): Context = Context(List(d))
}

/** declaration-level context: relative to a vocabulary, chooses a theory and an object-level context relative to it */
case class LocalEnvironment(theory: Theory, context: Context) extends SyntaxFragment {
  override def toString = s"$theory[$context]"
  def append(c: Context): LocalEnvironment = copy(context = context.append(c))
  def append(d: VarDecl): LocalEnvironment = append(Context(d))
}
object LocalEnvironment {
  val empty = LocalEnvironment(Theory.empty,Context.empty)
  def apply(thy: Theory): LocalEnvironment = LocalEnvironment(thy, Context.empty)
}

/** program-level context: provides the vocabulary and a local environment
  *
  * @param currentParent the path to the module in the vocabulary that current processing starts at;
  *                      also the bottom element of the stack of local environments
  * @param locals because checking must jump around between local environments, the letter are stored as a stack
  */
case class GlobalEnvironment(voc: Module, currentParent: Path,locals: List[LocalEnvironment]) {
  private def initLocal = if (locals.nonEmpty) this else copy(locals = List(LocalEnvironment(Theory(currentParent))))
  def currentLocal = initLocal.locals.head
  def theory = currentLocal.theory
  def context = currentLocal.context
  def push(t: Theory): GlobalEnvironment = push(LocalEnvironment(t))
  def push(e: LocalEnvironment): GlobalEnvironment = {
    val il = initLocal
    il.copy(locals = e::il.locals)
  }
  def pop() = {
    val il = initLocal
    il.copy(locals = il.locals.tail)
  }
  /** true if the local environment is given by the currentParent (as opposed to another one that we have pushed) */
  def inPhysicalTheory = initLocal.locals.length == 1
  def add(c: Context): GlobalEnvironment = {
    val il = initLocal
    il.copy(locals = il.locals.head.append(c) :: il.locals.tail)
  }
  def add(vd: VarDecl): GlobalEnvironment = add(Context(vd))

  def enter(n: String) = copy(currentParent = currentParent/n, locals = Nil)
  def add(d: Declaration) = copy(voc = voc.addIn(currentParent,d))
  def parentDecl = voc.lookupModule(currentParent).getOrElse {throw Checker.Error(voc, "unknown parent")}
}
object GlobalEnvironment {
  def apply(n: String): GlobalEnvironment = GlobalEnvironment(Module(n, false, Nil))
  def apply(m: Module): GlobalEnvironment = GlobalEnvironment(m, Path.empty, Nil)
}


// ***************** Programs and Declarations **************************************

/** top non-terminal; represents a set of declarations and an initial expression to evaluate */
case class Program(voc: List[Declaration], main: Expression) extends SyntaxFragment {
  override def toString = voc.mkString("\n") + "\n" + main
}

/** A declaration that nests other declarations.
  * It subsumes packages/namespaces, modules, classes, etc.
  *
  * Every module is closed or open relative to its base.
  * The base of an open module is the union of its closed includes.
  *
  * A closed module corresponds to a class/theory.
  * Closed modules encapsulate their body in a semantically meaningful way and
  * the language access to the body is only possible through specific syntax.
  * In particular, references to names in closed modules require an explicit include of the module.
  * The module name is irrelevant, and the reference is made by name only.
  *
  * Open modules are always available if their base is.
  * References to names in open modules are with [OpenRef] by path and do not require an explicit include.
  * In particular, an open module with empty base corresponds to a package.
  *
  * An open module with non-empty base are ideal for definitional extensions to the base such as theorems.
  * Name clashes are avoided because the module name is relevant.
  */
case class Module(name: String, closed: Boolean, decls: List[Declaration]) extends NamedDeclaration with HasChildren[Declaration] {
  override def toString = {
    val k = if (closed) "class" else "module"
    s"$k $name {\n${decls.mkString("\n").indent(2)}}"
  }

  /** after checking: all included modules */
  def supers = decls.collect {
    case id: Include => id.dom
  }
  /** after checking: all undefined included modules */
  def base = decls.collect {
    case id: Include if id.dfO.isEmpty => id.dom
  }
  /** after checking: all undefined symbol declarations */
  def undefined = decls.collect {
    case sd: SymbolDeclaration if sd.dfO.isEmpty => sd
  }

  /** for efficient sequential building of declarations: prepends to the last module
    * @param parent the path of the last module (not quite redundant when modules are nested)
    */
  private[p] def addIn(parent: Path, d: Declaration): Module = {
    if (parent.isRoot) copy(decls = d::decls)
    else {
      decls.headOption match {
        case Some(m: Module) if m.name.contains(parent.head) =>
          val mA = m.addIn(parent.tail, d)
          copy(decls = mA::decls.tail)
        case _ => throw Checker.Error(d,"unexpected path")
      }
    }
  }

  def append(d: Declaration) = copy(decls = decls ::: List(d))

  /** dereferences a path inside this module, returns the result followed by its ancestors */
  def lookupPathAndParents(path: Path, parents: List[NamedDeclaration]): Option[List[NamedDeclaration]] = path.names match {
    case Nil => Some(this::parents)
    case hd::_ => lookupO(hd).flatMap {
      case m:Module => m.lookupPathAndParents(path.tail, this::parents)
      case d:NamedDeclaration if path.tail.names.isEmpty => Some(d::parents)
      case _ => None
    }
  }
  def lookupPath(path: Path) = lookupPathAndParents(path, Nil).map(_.head)

  /** like lookupPath but with sharper return type, should also be called on checked paths */
  def lookupModule(path: Path): Option[Module] = lookupPath(path) match {
    case s@Some(m: Module) => Some(m)
    case _ => None
  }

  /** dereferences an ambiguous relative path: looks up par/p, par.up/p, par.up.up/p, ... , p and returns the first that exists */
  def lookupRelativePath(par: Path, p: Path): Option[(Path, NamedDeclaration)] = {
    val pp = par/p
    lookupPath(pp) match {
      case Some(d) => Some((pp,d))
      case None =>
        if (par.isRoot)
          None
        else
          lookupRelativePath(par.up,p)
    }
  }
}

object Module {
  def anonymous(decls: List[Declaration]) = Module("", false, decls)
}

/** parent of all declarations that do not nest other declarations */
sealed trait AtomicDeclaration extends Declaration {
  def tp: Type
  val dfO: Option[Object]
}

/** include within a module */
case class Include(dom: Path, dfO: Option[Expression], realize: Boolean) extends UnnamedDeclaration with AtomicDeclaration {
  def tp = ClassType(Theory(dom))
  override def toString = {
    val kw = if (realize) "realize" else "include"
    val dfS = dfO match {case None | Some(null) => "" case Some(d) => " = " + d.toString}
    kw + " " + dom + dfS
  }
}

/** parent class of all declarations that introduce symbols, e.g., type, function, predicate symbols */
sealed trait SymbolDeclaration extends NamedDeclaration with AtomicDeclaration {
  def kind: String // expression, type, ...
  def tpSep: String // ":", "<", ...
  override def toString = {
    val tpS = if (tp == null || tp == AnyType) "" else " " + tpSep + " " + tp.toString
    val dfOS = dfO match {case Some(t) => " = " + t case None => ""}
    kind + " " + name+tpS+dfOS
  }
}

/** declares a type symbol
  * @param tp the upper type bound, [AnyType] if unrestricted, null if to be inferred during checking
  */
case class TypeDecl(name: String, tp: Type, dfO: Option[Type]) extends SymbolDeclaration {
  def kind = "type"
  def tpSep = "<"
}

/** declares a typed symbol
  * @param tp the type, null if to be inferred during checking
  */
case class ExprDecl(name: String, tp: Type, dfO: Option[Expression], mutable: Boolean) extends SymbolDeclaration {
  def kind = "val"
  def tpSep = ":"
}

// ***************** Theories **************************************

/** theories choose a scope within a diagram by describing the accessible modules */
case class Theory(parts: List[Path]) extends SyntaxFragment {
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
  def apply(p: Path): Theory = Theory(List(p))
}

// ************************** Types and Expressions ************************

// Some classes dealing with symbol references and scoping are shared between types and expressions

/** reference to a symbol from an open theory, via an implementation of its base (if non-trivial) */
case class OpenRef(path: Path, via: Option[Expression]) extends Expression with Type {
  override def toString = {
    val viaS = via match {case Some(v) => "[" + v + "]" case None => ""}
    path + viaS
  }
}

/** reference to a symbol from an included theory */
case class ClosedRef(n: String) extends Expression with Type {
  override def toString = n
}

/** an object from a different local environment that is translated by o into the current local environment
  *
  * written o.x
  * If T |- o: S and S |- t : A : type, then T |- o.t : o.A : type
  * In particular, x must be closed and relative to the domain of o, not relative to the current context.
  * o must be a morphism into the current context, and o.x can be seen as the morphism application o(t).
  */
sealed trait OwnedObject extends Object {
  /** the translation, must evaluate to an [[Instance]] */
  def owner: Expression
  /** the original object */
  def owned: Object
  override def toString = owner + "." + owned
}

/**
  * expressions translated into another context
  *
  * If t is ClosedRef(n), this is the usual field access o.n known from OOP. See also [[Expression.field]]
  * By allowing arbitrary terms, we can delay traversing expressions, which might have to duplicate owner.
  */
case class OwnedExpr(owned: Expression, owner: Expression) extends Expression with OwnedObject

/** types translated to another environment
  *
  * Defined types are known from the outside and normalize to their definiens.
  * Undefined types are abstract from the outside even after defining them during instance creation.
  * Accessing them requires a pure owner and returns an unknown type.
  * The only way to create values for it is by calling methods on an instance that is
  * statically known to be equal when restricted to the class declaring the type field.
  */
// checker must ensure owner is Pure (compare Scala path types: owner must be variable to separate side effects from type field access.)
// interpreter invariant: semantics should not depend on types other than class refs, computation of types should never be needed,
// i.e., removing all types from declarations and type fields from modules/instances should be allowed
case class OwnedType(owned: Type, owner: Expression) extends Type with OwnedObject

// ***************** Types **************************************

/** an omitted type that is to be filled in during type inference */
sealed class UnknownType(var tp: Type) extends Type {
  override def known = tp != null
  override def skipUnknown: Type = if (known) tp.skipUnknown else this
  override def toString = if (known) tp.toString else "???"
}

/** the type of instances of a theory */
case class ClassType(domain: Theory) extends Type {
  override def toString = domain.toString
}

/** the type of instances of any theory */
object AnyStructure {
  def apply() = ClassType(Theory(Nil))
  def unapply(t: Type) = t match {
    case ClassType(Theory(Nil)) => Some(())
    case _ =>
  }
}

/** type of quotations of terms of a given type from a different environment, e.g., for inductive types, polynomials
  *
  * can be seen as the variant of OwnedType without owner
  */
case class ExprsOver(scope: LocalEnvironment, tp: Type) extends Type {
  override def toString = s"<$scope>$tp"
}

/** atomic built-in base types */
sealed abstract class BaseType(name: String) extends Type {self =>
  override def toString = name
}
object BaseType {
  val B = BoolType
  val I = IntType
  val R = RatType
  val S = StringType
  def L(e: Type) = ListType(e)
}
/** 0 elements */
case object EmptyType extends BaseType("empty")
/** 1 element */
case object UnitType extends BaseType("unit")
/** 2 elements */
case object BoolType extends BaseType("bool")
/** integer numbers */
case object IntType extends BaseType("int")
/** rationals numbers */
case object RatType extends BaseType("rat")
/** strings (exactly as implemented by Scala) */
case object StringType extends BaseType("string")
/** universal type of all expressions */
case object AnyType extends BaseType("any")

/** auxiliary class for built-in type operators */
sealed abstract class TypeOperator(val children: List[Type]) extends Type

/** functions (non-dependent) */
case class FunType(ins: List[Type], out: Type) extends TypeOperator(ins:::List(out)) {
  override def toString = (if (ins.length == 1) ins.head else ProdType(ins)) + " -> " + out
}

/** tuples (non-dependent Cartesian product) */
case class ProdType(comps: List[Type]) extends TypeOperator(comps) {
  override def toString = comps.mkString("(",", ", ")")
}
/** homogeneous lists */
case class ListType(elem: Type) extends TypeOperator(List(elem)) {
  override def toString = s"List[$elem]"
}
/** matches a list type, possibly specializing an [[UnknownType]] */
object ListOrUnknownType {
  def unapply(t: Type) = t match {
    case ListType(e) => Some(e)
    case u:UnknownType =>
      val e = Type.unknown
      u.tp = ListType(e)
      Some(e)
    case _ => None
  }
}
/** optional values */
case class OptionType(elem: Type) extends TypeOperator(List(elem)) {
  override def toString = s"Option[$elem]"
}

// ***************** Expressions **************************************

// **************************** introduction/elimination forms for built-in types

/** instance of a theory, introduction form for [[ClassType]] */
case class Instance(theory: Path, decls: List[AtomicDeclaration]) extends Expression with HasChildren[Declaration] with MutableExpressionStore {
  /** non-null exactly for run-time instances, which additionally carry the current values of all fields */
  private[p] var fields: List[MutableExpression] = null
  /** true if this is a run-time instance, e.g., has been initialized already */
  private[p] def isRuntime = fields != null
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

/** a quoted expressions; introduction form of [[ExprsOver]] */
case class ExprOver(scope: LocalEnvironment, expr: Expression) extends Expression {
  override def toString = s"<{$scope} $expr>"
}
/** backquote/evaluation inside a [[ExprsOver]] */
case class Eval(syntax: Expression) extends Expression {
  override def toString = s"`$syntax`"
}

/** anonymous function, introduction form for [[FunType]] */
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

/** function application, elimination form for [[FunType]] */
case class Application(fun: Expression, args: List[Expression]) extends Expression {
  override def toString = {
    fun match {
      case BaseOperator(o: InfixOperator,_) => args.mkString("("," " + o.symbol + " ",")")
      case BaseOperator(o: PrefixOperator,_) => o.symbol + args.mkString
      case _ => fun + args.mkString("(",", ",")")
    }
  }
}

/** tuples, introduction form for [[ProdType]] */
case class Tuple(comps: List[Expression]) extends Expression {
  override def toString = comps.mkString("(", ", ", ")")
}

/** projection, elimination form for [[ProdType]]
  * @param index tuple component, starting at 1
  */
case class Projection(tuple: Expression, index: Int) extends Expression {
  override def toString = s"$tuple.$index"
}

/** lists, introduction form for [[ListType]] */
case class ListValue(elems: List[Expression]) extends Expression {
  override def toString = s"List(${elems.mkString(",")})"
}
/** list elements access, elimination form for [[ListType]]
  * @param position must evaluate to an [[IntValue]] between 0 and length-1; type-checking is undecidable and over-approximates
  */
case class ListElem(list: Expression, position: Expression) extends Expression {
  override def toString = s"$list($position)"
}

/** base values, introduction forms of [[BaseType]] */
sealed abstract class BaseValue(val value: Any, val tp: BaseType) extends Expression

/** element of [[UnitType]] */
case object UnitValue extends BaseValue((), UnitType) {
  override def toString = "()"
}

/** elements of [[BoolType]] */
case class BoolValue(v: Boolean) extends BaseValue(v, BoolType) {
  override def toString = value.toString
}

/** elements of [[IntType]] */
case class IntValue(v: Int) extends BaseValue(v, IntType) {
  override def toString = value.toString
}

/** elements of [[RatType]] */
case class RatValue(enum: Int, denom: Int) extends BaseValue(enum/denom, RatType) {
  override def toString = enum.toString + "/" + denom.toString
}

/** helper object to construct/pattern-match numbers such that [[IntType]] is a subtype of [[RatType]] */
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

/** elements of [[StringType]] */
case class StringValue(v: String) extends BaseValue(v, StringType) {
  override def toString = "\"" + String.escape(v) + "\""
}

object String {
  def escape(s:String) = s.replace("\\", "\\\\").replace("\"","\\\"")
}

/** built-in operators, bundles various elimination forms for the built-in types
  * @param operator the operator
  * @param tp its type (most operators are ad-hoc polymorphic), null if to be infered during checking
  */
case class BaseOperator(operator: Operator, tp: Type) extends Expression

// ************************** Standard programming language objects

/** local variable declaration */
case class VarDecl(name: String, tp: Type, dfO: Option[Expression], mutable: Boolean) extends Expression with Named {
  def defined = dfO.isDefined
  override def toString = {
    val tpS = if (tp == null) "???" else tp.toString
    val vlS = dfO match {case Some(v) => " = " + v.toString case None => ""}
    s"$name: $tpS$vlS"
  }
}
object VarDecl {
  def apply(n: String, tp: Type, dfO: Option[Expression] = None): VarDecl = VarDecl(n, tp, dfO, false)
}
/** reference to local variable */
case class VarRef(name: String) extends Expression {
  override def toString = name
}
/** assignment to mutable local variables */
case class Assign(target: Expression, value: Expression) extends Expression {
  override def toString = s"$target = $value"
}

/** sequence of expressions, ;-operator
  *
  * evaluates to its last element, variable declarations are in scope till the end of their block
  */
case class Block(exprs: List[Expression]) extends Expression {
  override def toString = exprs.mkString("{", " ", "}")
}

/** if-then-else, ternary operators, can be seen as elimination form of [[BoolType]] */
case class IfThenElse(cond: Expression, thn: Expression, els: Option[Expression]) extends Expression {
  override def toString = {
    val elsS = els.map(e => " else " + e).getOrElse("")
    s"if $cond $thn$elsS"
  }
}

/** for-loop, can be seen as elimination form of [[ListType]]
  * @param range must evaluate to list
  */
case class For(name: String, range: Expression, body: Expression) extends Expression

/** while-loop */
case class While(cond: Expression, body: Expression) extends Expression

// *********************************** Operators *****************************

/** parent class of all operators
  *
  * Operators carry concrete syntax and typing information so that their processing is controlled by the operator,
  * not by the parser/checker/printer.
  * For the latter to be able to access this information, all operators must be listed in the companion object [[Operator]] */
sealed abstract class Operator(val symbol: String) {
  def types: List[FunType]
  def polyTypes(u: UnknownType): List[FunType] = Nil
}

/** operators with binary infix notation */
sealed abstract class InfixOperator(s: String, val precedence: Int, val flexary: Boolean) extends Operator(s)
/** operators with prefix notation */
sealed abstract class PrefixOperator(s: String) extends Operator(s)

// for type abbreviations
import BaseType._
/** arithmetic operators */
sealed trait Arithmetic {
  val types = List(I<--(I,I), R<--(R,R), R<--(I,R), R<--(R,I))
}
/** boolean connectives */
sealed trait Connective {
  val types = List(B<--(B,B))
}
/** comparison operators for base values */
sealed trait Comparison {
  val types = List(B<--(I,I), B<--(R,R), B<--(I,R), B<--(R,I), B<--(S,S), B<--(B,B))
}
/** polymorphic (in)equality at any type */
sealed trait Equality extends Operator {
  def types = Nil
  override def polyTypes(u: UnknownType) = List(u<--(u,u))
}

case object Plus extends InfixOperator("+", 0, false) with Arithmetic {
  override def polyTypes(u: UnknownType) = List(L(u)<--(L(u),L(u)))
}
case object Minus extends InfixOperator("-", 0, false) with Arithmetic
case object Times extends InfixOperator("*", 10, true) with Arithmetic
case object Divide extends InfixOperator("/", 10, false) {
  val types = List(R<--(I,I), R<--(R,R), R<--(I,R), R<--(R,I))
}
case object Power extends InfixOperator("^", 20, false) {
  val types = List(I<--(I,I), R<--(R,R), R<--(I,R), R<--(R,I))
}

case object And extends InfixOperator("&", -20, true) with Connective
case object Or extends InfixOperator("|", -20, true) with Connective

case object Less extends InfixOperator("<", -10, false) with Comparison
case object LessEq extends InfixOperator("<=", -10, false) with Comparison
case object Greater extends InfixOperator(">", -10, false) with Comparison
case object GreaterEq extends InfixOperator(">=", -10, false) with Comparison

case object Equal extends InfixOperator("==", -10, false) with Equality
case object Inequal extends InfixOperator("!=", -10, false) with Equality

case object UMinus extends PrefixOperator("-") {
  val types = List(I<--I, R<--R)
}
case object Not extends PrefixOperator("!") {
  val types = List(B<--B)
}

object Operator {
  val infixes = List(Plus, Minus, Times, Divide, Power,
                     And, Or,
                     Less, LessEq, Greater, GreaterEq,
                     Equal, Inequal)
  val prefixes = List(UMinus,Not)
}