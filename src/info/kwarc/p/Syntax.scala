package info.kwarc.p

case class Location(file: File, from: Int, to: Int) {
  override def toString = file.toJava.getName + s"#$from:$to"
}


// ***************************** root classes and auxiliary data structures

/** parent of all errors */
abstract class PError(msg: String) extends Exception(msg)

/** implementation errors */
case class IError(msg: String) extends PError(msg)

/** run-time errors */
case class DivisionByZero() extends PError("")

/** parent of all classes in the AST */
sealed abstract class SyntaxFragment {
  private[p] var loc: Location = null // set by parser to remember location in source
  /** moves over mutable fields, may be called after performing traversals
    * if the resulting expression is "the same" as the original in some sense
    * if needed, it is usually to implement the traversal using also SyntaxFragment.matchC in the first place
    */
  def copyFrom(sf: SyntaxFragment): this.type = {
    loc = sf.loc
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
  def apply(n: String): Path = Path(List(n))
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
  /** true if this type is definitely finite (in complex cases, this may be false for finite types)
    * only reliable for fully normalized types
    */
  def finite: Boolean
  def power(n: Int) = ProdType(Range(1,n).toList.map(_ => this))
}
object Type {
  private var unknownCounter = -1
  def unknown() = {unknownCounter += 1; new UnknownType(unknownCounter, null)}
  val unbounded = AnyType
  /** normalizes what can be done context-freely, in particular removes unknown types */
  def normalize(tp: Type) = IdentityTraverser(tp)(GlobalContext(""),())
}

/** typed expressions */
sealed trait Expression extends Object {
  def field(f: String) = OwnedExpr(this, ClosedRef(f))
}

/** parent of all structuring classes like module, symbol declarations */
sealed abstract class Declaration extends SyntaxFragment with MaybeNamed {
  private[p] var subsumed = false // can be used to mark that this is redundant due to a later more specific one
  private[p] var subsuming = false // can be used to mark that this makes a previous declarations redundant
  private[p] var global = false // true for declarations in open modules, which require OpenRef
  override def copyFrom(sf: SyntaxFragment): this.type = {
    super.copyFrom(sf)
    sf match {
      case d: Declaration =>
        subsuming = d.subsuming
        subsumed = d.subsumed
        global = d.global
      case _ =>
    }
    this
  }
}
sealed abstract class NamedDeclaration extends Declaration with Named {
}
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
      else if (Type.normalize(sd1.tp) == Type.normalize(sd2.tp)) compareOO(sd1.dfO,sd2.dfO)
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

abstract class Context[A] extends SyntaxFragment with HasChildren[VarDecl] {
  def append(c: LocalContext): A
  def append(vd: VarDecl): A = append(LocalContext(vd))
  def local: LocalContext
  def decls = local.variables
  def getOutput = local.decls.find(vd => vd.name == "" && vd.output).map(_.tp)
}

/** object-level context: relative to a vocabulary and a choice of theory in it
  * inner-most variables occur first and are found first by lookup
  */
case class LocalContext(variables: List[VarDecl]) extends Context[LocalContext] {
  override def toString = variables.mkString(", ")
  def local = this
  def append(c: LocalContext) = copy(variables = c.variables.reverse ::: variables)
  def substitute(es: List[Expression]) = {
    if (variables.length != es.length) throw IError("unexpected number of values")
    val defs = (variables zip es.reverse).map {case (vd,e) => VarDecl(vd.name, null, Some(e))}
    Substitution(defs)
  }
}
object LocalContext {
  val empty = LocalContext(Nil)
  def apply(d: VarDecl): LocalContext = LocalContext(List(d))
}

case class Substitution(decls: List[VarDecl]) extends HasChildren[VarDecl] {
  def append(n: String, e: Expression) = Substitution(VarDecl(n,null,Some(e))::decls)
}

/** declaration-level context: relative to a vocabulary, chooses a theory and an object-level lc relative to it */
case class RegionalContext(theory: Theory, owner: Option[Expression], local: LocalContext) extends Context[RegionalContext] {
  override def toString = owner.getOrElse(theory).toString + s"{$local}"
  def physical = theory.physical && owner.isEmpty
  def append(c: LocalContext) = copy(local = local.append(c))
}
object RegionalContext {
  val empty = RegionalContext(Theory.empty, None, LocalContext.empty)
  def apply(thy: Theory, owner: Option[Expression] = None): RegionalContext =
    RegionalContext(thy, owner, LocalContext.empty)
  def apply(p: Path): RegionalContext = RegionalContext(PhysicalTheory(p))
}

/** program-level lc: provides the vocabulary and a local environment
  *
  * @param currentParent the path to the module in the vocabulary that current processing starts at;
  *                      also the bottom element of the stack of local environments
  * @param locals because checking must jump around between local environments, the letter are stored as a stack
  */
case class GlobalContext private (voc: Module, regions: List[(Boolean,RegionalContext)]) extends Context[GlobalContext] {
  def currentRegion = regions.head._2
  def currentIsTransparent = regions.head._1
  def theory = currentRegion.theory
  def local = LocalContext(regions.takeWhile(_._1).flatMap(_._2.local.decls))
  def push(t: Theory, owner: Option[Expression] = None): GlobalContext = push(RegionalContext(t,owner))
  def push(e: RegionalContext): GlobalContext = copy(regions = (false,e)::regions)
  def pop() = copy(regions = regions.tail)
  /** true if the local environment is given by the current parent(s) (as opposed to other ones that we have pushed) */
  def inPhysicalTheory = regions.forall(_._2.physical)
  def append(c: LocalContext) = copy(regions = (regions.head._1, regions.head._2.append(c)) :: regions.tail)

  private def currentParent: Path = {
    if (!inPhysicalTheory) throw IError("not in physical theory")
    currentRegion.theory.pathO.get
  }
  def enter(n: String) = copy(regions = (true, RegionalContext(currentParent/n)) :: regions)
  def add(d: Declaration) = copy(voc = voc.addIn(currentParent,d))
  def parentDecl = voc.lookupModule(currentParent).getOrElse {throw Checker.Error(voc, "unknown parent")}
  /** dereferences an ambiguous relative path: looks up in transparent physical parent regions and returns the first that exists */
  def resolvePath(p: Path): Option[(Path, NamedDeclaration)] = {
    if (!inPhysicalTheory) return None


    val pp = currentParent/p
    voc.lookupPath(pp) match {
      case Some(d) => Some((pp,d))
      case None =>
        if (regions.length > 1 && currentIsTransparent) {
          // current region is transparent and there is a previous one to try
          pop.resolvePath(p)
        } else None
    }
  }
  def resolveName(obj: Object): Option[(Object,Option[NamedDeclaration])] = {
    def make(e: Object) = if (e == obj) obj else e.copyFrom(obj)
    val n = obj match {
      case VarRef(n) => n
      case ClosedRef(n) => n
      case _ => return Some((obj,None))
    }
    // try finding local variable n in context
    lookupO(n).foreach {_ =>
      return Some((make(VarRef(n)),None))
    }
    // try finding n declared regionally in current or included module
    lookupRegional(n).foreach {d =>
      return Some((make(ClosedRef(n)),Some(d)))
    }
    // try finding n declared globally in current module or parent modules
    resolvePath(Path(n)) foreach {case (p,d) =>
      return Some((make(OpenRef(p)),Some(d)))
    }
    // give up
    None
  }

  def lookupRegional(name: String): Option[NamedDeclaration] = {
    val mod = if (inPhysicalTheory) parentDecl else theory.toModule
    // look in the current module for a primitive or previously merged declaration
    mod.lookupO(name) match {
      case Some(nd: NamedDeclaration) if !nd.global => return Some(nd)
      case _ =>
    }
    // look in included modules
    val ds = mod.supers.flatMap {p =>
      voc.lookupPath(p/name).toList
    }.filter(d => !d.global && !d.subsumed)
    if (ds.isEmpty) {
      if (regions.length > 1 && currentIsTransparent) {
        // look in transparent enclosing regions
        pop.lookupRegional(name)
      } else
        None
    } else {
      // find the most defined one
      var res = ds.head
      ds.tail.foreach {d =>
        Declaration.compare(res,d) match {
          case Declaration.Subsumes | Declaration.Identical =>
          case Declaration.SubsumedBy => res = d
          case Declaration.Independent | Declaration.Clashing => throw IError("multiple incompatible declarations found")
        }
      }
      Some(res)
    }
  }

}
object GlobalContext {
  def apply(n: String): GlobalContext = GlobalContext(Module(n, false, Nil))
  def apply(m: Module): GlobalContext = GlobalContext(m, List((true,RegionalContext(Path.empty))))
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
  * References to names in open modules are with [[OpenRef]] by path and do not require an explicit include.
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
    if (parent.isRoot) copy(decls = d::decls).copyFrom(this)
    else {
      decls.headOption match {
        case Some(m: Module) if m.name.contains(parent.head) =>
          val mA = m.addIn(parent.tail, d)
          copy(decls = mA::decls.tail).copyFrom(this)
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
  def tp = ClassType(PhysicalTheory(dom))
  override def toString = {
    val kw = if (realize) "realize" else "include"
    val dfS = dfO match {case None | Some(null) => "" case Some(d) => " = " + d.toString}
    kw + " " + dom + dfS
  }
}

object Include {
  def apply(p: Path, dfO: Option[Expression] = None): Include = Include(p, dfO, false)
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

/** theories are anonyomous modules */
case class Theory(decls: List[Declaration]) extends SyntaxFragment {
  override def toString = {
    this match {
      case ExtendedTheory(p,ds) => p.toString + (if  (ds.isEmpty) "" else " " + Theory(ds).toString)
      case _ => decls.mkString("{", ", ", "}")
    }
  }
  def pathO = decls match {
    case Include(p,None,_) :: Nil => Some(p)
    case _ => None
  }
  def physical = pathO.isDefined
  private[p] var isFlat = false
  override def copyFrom(sf: SyntaxFragment): this.type = {
    super.copyFrom(sf)
    sf match {
      case t: Theory => isFlat = t.isFlat
      case _ =>
    }
    this
  }
  def domain = decls.collect {
    case nd: NamedDeclaration => nd.name
  }
  def sub(that: Theory) = this.decls.forall(d => that.decls contains d)
  def union(that: Theory) = Theory(this.decls ::: that.decls)
  override def equals(that: Any) = that match {
    case that: Theory =>
      // hardcode associativity, commutativity, idempotency of union
      decls.length == that.decls.length && (this sub that) && (that sub this)
    case _ => false
  }
  override def hashCode(): Int = decls.sortBy(_.toString).hashCode()

  def toModule = Module("",true,decls)
  def lookupPath(path: Path) = {
    toModule.lookupPath(path)
  }
}
object Theory {
  def empty = Theory(Nil)
}

object PhysicalTheory {
  def apply(p: Path): Theory = Theory(List(Include(p)))
  def unapply(thy: Theory) = thy.decls match {
    case Include(p,None,false) :: Nil => Some(p)
    case _ => None
  }
}

object ExtendedTheory {
  def apply(p: Path, sds: List[SymbolDeclaration]): Theory = Theory(Include(p) :: sds)
  def unapply(thy: Theory) = thy.decls match {
    case Include(p,None,_) :: ds if ds.forall(_.isInstanceOf[SymbolDeclaration]) =>
      Some((p, ds.map(_.asInstanceOf[SymbolDeclaration])))
    case _ => None
  }
}

// ************************** Types and Expressions ************************

// Some classes dealing with symbol references and scoping are shared between types and expressions

/** reference to a symbol from an open theory */
case class OpenRef(path: Path) extends Expression with Type {
  override def toString = {
    "." + path
  }
  def finite = false
}

/** reference to a symbol from an included theory */
case class ClosedRef(n: String) extends Expression with Type {
  override def toString = n
  def finite = false
}

/** an object from a different local environment that is translated by o into the current local environment
  *
  * written o.x
  * If T |- o: S and S |- t : A : type, then T |- o.t : o.A : type
  * In particular, x must be closed and relative to the domain of o, not relative to the current lc.
  * o must be a morphism into the current lc, and o.x can be seen as the morphism application o(t).
  */
sealed trait OwnedObject extends Object {
  /** the translation, must evaluate to an [[Instance]] */
  def owner: Expression
  /** the original object */
  def owned: Object
  override def toString = owner + "." + owned
}

/**
  * expressions translated into another lc
  *
  * If t is ClosedRef(n), this is the usual field access o.n known from OOP. See also [[Expression.field]]
  * By allowing arbitrary terms, we can delay traversing expressions, which might have to duplicate owner.
  */
case class OwnedExpr(owner: Expression, owned: Expression) extends Expression with OwnedObject

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
case class OwnedType(owner: Expression, owned: Type) extends Type with OwnedObject {
  def finite = false
}

// ***************** Types **************************************

/** an omitted type that is to be filled in during type inference */
sealed class UnknownType(private var id: Int, private var _tp: Type) extends Type {
  def tp = if (known) _tp.skipUnknown else null
  override def known = {_tp != null && _tp.known}
  def set(t: Type): Unit = {
    if (known)
      throw IError("type already inferred")
    if (_tp == null) {
      // println(s"solving $this as $t")
      _tp = t.skipUnknown
    } else _tp match {
      case u:UnknownType =>
        u.set(t)
      case _ => throw IError("impossible case")
    }
  }
  override def skipUnknown: Type = if (known) _tp.skipUnknown else this
  override def toString = if (known) _tp.toString else "???"+id
  def finite = if (known) skipUnknown.finite else false
}

/** the type of instances of a theory */
case class ClassType(domain: Theory) extends Type {
  override def toString = domain.toString
  def finite = false
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
case class ExprsOver(scope: Theory, tp: Type) extends Type {
  override def toString = s"<$scope>$tp"
  def finite = false
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
  def L(e: Type) = CollectionKind.List(e)
  def O(e: Type) = CollectionKind.Option(e)
}
/** 0 elements */
case object EmptyType extends BaseType("empty") {
  def finite = true
}
/** 1 element */
case object UnitType extends BaseType("unit") {
  def finite = true
}
/** 2 elements */
case object BoolType extends BaseType("bool") {
  def finite = true
}
/** integer numbers */
case object IntType extends BaseType("int") {
  def finite = false
}
/** rationals numbers */
case object RatType extends BaseType("rat") {
  def finite = false
}
/** strings (exactly as implemented by Scala) */
case object StringType extends BaseType("string") {
  def finite = false
}
/** universal type of all expressions */
case object AnyType extends BaseType("any") {
  def finite = false
}

/** interval of integers, unbounded if bounds absent, including lower and upper bound if present */
case class IntervalType(lower: Option[Expression], upper: Option[Expression]) extends Type {
  def finite = lower.isDefined && upper.isDefined
  def concrete = lower.forall(_.isInstanceOf[IntValue]) && upper.forall(_.isInstanceOf[IntValue])
}

/** functions (non-dependent) */
case class FunType(ins: List[Type], out: Type) extends Type {
  override def toString = (if (ins.length == 1) ins.head else ProdType(ins)) + " -> " + out
  def finite = (out::ins).forall(_.finite)
}

/** tuples (non-dependent Cartesian product) */
case class ProdType(comps: List[Type]) extends Type {
  override def toString = comps.mkString("(",", ", ")")
  def finite = comps.forall(_.finite)
}
/** homogeneous collections, unifies lists, finite sets, options, etc.
  * all types are Curry-subquotients of lists, i.e., there is only one introduction form for all of them
  */
case class CollectionType(elem: Type, kind: CollectionKind) extends Type {
  override def toString = {
    s"$kind[$elem]"
  }
  def finite = kind.idemp && elem.finite
}
case class CollectionKind(idemp: Boolean, comm: Boolean, sizeOne: Boolean) {
  override def toString = CollectionKind.allKinds.find(_._2 == this).get._1
  def apply(a: Type) = CollectionType(a, this)
  def unapply(a: Type) = a match {
    case CollectionType(e,k) if k == this => Some(e)
    case _ => None
  }
  def sub(that: CollectionKind) = {
    this.sizeOne || ((!this.idemp || that.idemp) && (!this.comm || that.comm))
  }
  def union(that: CollectionKind) = {
    if (this.sizeOne) that else if (that.sizeOne) this else
    CollectionKind(this.idemp || that.idemp, this.comm || that.comm, false)
  }
  def inter(that: CollectionKind) = {
    if (this.sizeOne || that.sizeOne) CollectionKind.Option else
    CollectionKind(this.idemp && that.idemp, this.comm && that.comm, false)
  }
}

object CollectionKind {
  val List = CollectionKind(false,false,false)
  val Set = CollectionKind(true,true,false)
  val Bag = CollectionKind(false,true,false)
  val UList = CollectionKind(true,false,false)
  val Option = CollectionKind(true,true,true)
  val allKinds = scala.List("List" -> this.List, "UList" -> this.UList, "Bag" -> this.Bag, "Set" -> this.Set, "Option" -> this.Option)
  val allKeywords = allKinds.map(_._1)
}

// ***************** Expressions **************************************

// **************************** introduction/elimination forms for built-in types

/** instance of a theory, introduction form for [[ClassType]] */
// TODO: dependent modules, i.e., theory is an OwnedTerm(o,ClosedRef(m))
case class Instance(theory: Theory) extends Expression with MutableExpressionStore {
  override def toString = if (isRuntime) {
      s"instance of $theory"
    } else
      theory.toString
  /** non-null exactly for run-time instances, which additionally carry the current values of all fields */
  private[p] var fields: List[MutableExpression] = null
  /** true if this is a run-time instance, e.g., has been initialized already */
  private[p] def isRuntime = fields != null
}

/** a quoted expressions; introduction form of [[ExprsOver]] */
case class ExprOver(scope: Theory, expr: Expression) extends Expression {
  override def toString = s"<{$scope} $expr>"
}
/** backquote/evaluation inside a [[ExprsOver]] */
case class Eval(syntax: Expression) extends Expression {
  override def toString = s"`$syntax`"
}

/** anonymous function, introduction form for [[FunType]] */
case class Lambda(ins: LocalContext, body: Expression) extends Expression {
  // used at run-time to store the frame relative to which the body must be interpreted when the function is applied
  private[p] var frame: RegionalEnvironment = null
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

/** collections, introduction form for [[CollectionType]] */
case class CollectionValue(elems: List[Expression]) extends Expression {
  override def toString = elems.mkString("[", ",", "]")
}
/** list elements access, elimination form for non-commutative [[CollectionType]]s
  * @param position must evaluate to an [[IntValue]] between 0 and length-1; type-checking is undecidable and over-approximates
  */
case class ListElem(list: Expression, position: Expression) extends Expression {
  override def toString = s"$list[$position]"
}

case class Quantifier(univ: Boolean, vars: LocalContext, body: Expression) extends Expression {
  def binder = if (univ) "forall" else "exists"
  override def toString = s"($binder $vars.$body)"
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
case class IntValue(v: BigInt) extends BaseValue(v, IntType) {
  override def toString = value.toString
}

/** elements of [[RatType]] */
case class RatValue(enum: BigInt, denom: BigInt) extends BaseValue(enum/denom, RatType) {
  override def toString = enum.toString + "/" + denom.toString
}

/** helper object to construct/pattern-match numbers such that [[IntType]] is a subtype of [[RatType]] */
object IntOrRatValue {
  def apply(e:BigInt, d: BigInt): BaseValue = {
    val g = e gcd d
    val eg = e/g
    val dg = d/g
    if (dg == 1) IntValue(e) else RatValue(eg,dg)
  }
  def unapply(e: Expression) = e match {
    case IntValue(i) => Some((i,BigInt(1)))
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
case class BaseOperator(operator: Operator, tp: Type) extends Expression {
  override def toString = "(" + operator.symbol + ":" + tp + ")"
}

// ************************** Standard programming language objects

/** local variable declaration
  * @param mutable write access allowed at run time
  * @param output the variable has no value (unless defined) and can only be written to
  *               unnamed output variables are the target of return statements
  */
case class VarDecl(name: String, tp: Type, dfO: Option[Expression], mutable: Boolean, output: Boolean) extends Expression with Named {
  def defined = dfO.isDefined
  override def toString = {
    val sep = if (output) "#" else ":"
    val tpS = if (tp == null) "???" else tp.toString
    val vlS = dfO match {case Some(v) => " = " + v.toString case None => ""}
    s"$name$sep $tpS$vlS"
  }
}
object VarDecl {
  def apply(n: String, tp: Type, dfO: Option[Expression] = None, mutable: Boolean = false): VarDecl = VarDecl(n, tp, dfO, mutable, false)
  def output(tp: Type) = VarDecl("", tp, None, false, true)
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
  * evaluates to its last element, variable declarations are in scope till the end of their block
  */
case class Block(exprs: List[Expression]) extends Expression {
  override def toString = exprs.mkString("{", "; ", "}")
}

/** if-then-else, ternary operators, can be seen as elimination form of [[BoolType]] */
case class IfThenElse(cond: Expression, thn: Expression, els: Option[Expression]) extends Expression {
  override def toString = {
    val elsS = els.map(e => " else " + e).getOrElse("")
    s"if $cond $thn$elsS"
  }
}

/** unifies pattern-matching and exception handling */
case class Match(expr: Expression, cases: List[MatchCase], handler: Boolean) extends Expression {
  override def toString = {
    val kw = if (handler) "handle" else "match"
    expr.toString + " " + kw + " {\n" + cases.mkString("\n") + "}"
  }
}

/** case in a match: context |- pattern -> body */
case class MatchCase(context: LocalContext, pattern: Expression, body: Expression) extends Expression {
  override def toString = pattern.toString + " -> " + body
}

/** for-loop, can be seen as elimination form of [[CollectionType]], behaves like map
  * @param range must evaluate to list
  */
case class For(vd: VarDecl, range: Expression, body: Expression) extends Expression {
  override def toString = s"for ${vd.name} in $range $body"
}

/** while-loop */
case class While(cond: Expression, body: Expression) extends Expression {
  override def toString = s"while $cond $body"
}

/** unifies return and throw statements */
case class Return(exp: Expression, thrw: Boolean) extends Expression {
  override def toString = {
    val kw = if (thrw) "throw" else "return"
    kw + " " + exp
  }
}

// *********************************** Operators *****************************

/** parent class of all operators
  *
  * Operators carry concrete syntax and typing information so that their processing is controlled by the operator,
  * not by the parser/checker/printer.
  * For the latter to be able to access this information, all operators must be listed in the companion object [[Operator]] */
sealed abstract class Operator(val symbol: String) {
  val length = symbol.length
  def types: List[FunType]
  def polyTypes(u: UnknownType): List[FunType] = Nil
  def makeExpr(args: List[Expression]) = Application(BaseOperator(this, Type.unknown), args)
}

/** operators with binary infix notation (flexary flag not supported yet) */
sealed abstract class InfixOperator(s: String, val precedence: Int, val flexary: Boolean) extends Operator(s) {
  def apply(l: Expression, r: Expression) = makeExpr(List(l,r))
}
/** operators with prefix notation */
sealed abstract class PrefixOperator(s: String) extends Operator(s) {
  def apply(e: Expression) = makeExpr(List(e))
}

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
  override def polyTypes(u: UnknownType) = List(B<--(u,u))
  def apply(tp: Type, l: Expression, r: Expression) =
    Application(BaseOperator(this,FunType(List(tp,tp),BoolType)), List(l,r))
  /** the operator to reduce after applying this operator on a list of pairs */
  def reduce: Operator
}

case object Plus extends InfixOperator("+", 0, true) with Arithmetic {
  override val types = (S<--(S,S))::Times.types
  override def polyTypes(u: UnknownType) = List(L(u)<--(L(u),L(u)))
}
case object Minus extends InfixOperator("-", 0, false) with Arithmetic
case object Times extends InfixOperator("*", 10, true) with Arithmetic
case object Divide extends InfixOperator("/", 10, false) {
  val types = List(R<--(I,I), R<--(R,R), R<--(I,R), R<--(R,I))
}
case object Minimum extends InfixOperator("min", 10, true) with Arithmetic
case object Maximum extends InfixOperator("max", 10, true) with Arithmetic

case object Power extends InfixOperator("^", 20, false) {
  val types = List(I<--(I,I), R<--(R,R), R<--(I,R), R<--(R,I))
}

case object In extends InfixOperator("in", -10, false) {
  val types = Nil
  override def polyTypes(u: UnknownType) =
    List(BoolType<--(u,CollectionKind.Set(u)))
}

case object Cons extends InfixOperator("-:", -10, false) {
  val types = Nil
  override def polyTypes(u: UnknownType) = List(L(u)<--(u,L(u)))
}

case object Snoc extends InfixOperator(":-:", -10, false) {
  val types = Nil
  override def polyTypes(u: UnknownType) = List(L(u)<--(L(u),u))
}

case object And extends InfixOperator("&", -20, true) with Connective {
  def apply(args: List[Expression]): Expression = args match {
    case Nil => BoolValue(true)
    case e::Nil => e
    case hd::tl => apply(hd, apply(tl))
  }
}
case object Or extends InfixOperator("|", -20, true) with Connective {
  def apply(args: List[Expression]): Expression = args match {
    case Nil => BoolValue(false)
    case e::Nil => e
    case hd::tl => apply(hd, apply(tl))
  }
}

case object Less extends InfixOperator("<", -10, false) with Comparison
case object LessEq extends InfixOperator("<=", -10, false) with Comparison
case object Greater extends InfixOperator(">", -10, false) with Comparison
case object GreaterEq extends InfixOperator(">=", -10, false) with Comparison

case object Equal extends InfixOperator("==", -10, false) with Equality {
  val reduce = And
}
case object Inequal extends InfixOperator("!=", -10, false) with Equality {
  val reduce = Or
}

case object UMinus extends PrefixOperator("-") {
  val types = List(I<--I, R<--R)
}
case object Not extends PrefixOperator("!") {
  val types = List(B<--B)
}

object Operator {
  val infixes = List(Plus, Minus, Times, Divide, Power, Minimum, Maximum,
                     And, Or,
                     Less, LessEq, Greater, GreaterEq,
                     In, Cons, Snoc,
                     Equal, Inequal)
  val prefixes = List(UMinus,Not)

  def simplify(o: Operator, as: List[Expression]): Expression = {
    o match {
      case pf: PrefixOperator =>
        ((pf,as.head)) match {
          case (UMinus,(IntOrRatValue(x,y))) => IntOrRatValue(-x,y)
          case (Not,BoolValue(b)) => BoolValue(!b)
        }
      case inf: InfixOperator =>
        (inf,as(0),as(1)) match {
          case (Plus,IntOrRatValue(u,v),IntOrRatValue(x,y)) => IntOrRatValue(u * y + v * x,v * y)
          case (Minus,IntOrRatValue(u,v),IntOrRatValue(x,y)) => IntOrRatValue(u * y - v * x,v * y)
          case (Times,IntOrRatValue(u,v),IntOrRatValue(x,y)) => IntOrRatValue(u * x,v * y)
          case (Minimum, IntOrRatValue(u,v), IntOrRatValue(x,y)) => IntOrRatValue((u*y) min (v*x), v*y)
          case (Maximum, IntOrRatValue(u,v), IntOrRatValue(x,y)) => IntOrRatValue((u*y) max (v*x), v*y)
          case (Divide,IntOrRatValue(u,v),IntOrRatValue(x,y)) =>
            if (x == 0) throw DivisionByZero() else IntOrRatValue(u * y,v * x)
          case (c: Comparison,IntOrRatValue(u,v),IntOrRatValue(x,y)) =>
            val d = u * y - v * x
            val s = if (d > 0) 1 else if (d < 0) -1 else 0
            (s,c) match {
              case (-1,Less | LessEq) |
                   (1,Greater | GreaterEq) |
                   (0,LessEq | GreaterEq) => BoolValue(true)
              case _ => BoolValue(false)
            }
          case (c: Comparison,BoolValue(l),BoolValue(r)) =>
            val b = c match {
              case Less => !l && r
              case LessEq => !l || r
              case Greater => l && !r
              case GreaterEq => l || !r
            }
            BoolValue(b)
          case (And,BoolValue(l),BoolValue(r)) => BoolValue(l && r)
          case (Or,BoolValue(l),BoolValue(r)) => BoolValue(l || r)
          case (Plus,StringValue(l),StringValue(r)) => StringValue(l + r)
          case (Plus,CollectionValue(l),CollectionValue(r)) => CollectionValue(l ::: r)
          case (e: Equality,l: BaseValue,r: BaseValue) =>
            // TODO: more types
            val b = ((e == Equal) == (l.value == r.value))
            BoolValue(b)
          case (e: Equality,Tuple(ls), Tuple(rs)) =>
            if (ls.length != rs.length) BoolValue(e != Equal)
            else {
              val lrs = (ls zip rs).map({case (l,r) => simplify(e, List(l,r))})
              simplify(e.reduce, lrs)
            }
          case (e: Equality,CollectionValue(ls), CollectionValue(rs)) =>
            // TODO: depends on the collection kind
            if (ls.length != rs.length) BoolValue(e != Equal)
            else {
              val lrs = (ls zip rs).map({case (l,r) => simplify(e, List(l,r))})
              simplify(e.reduce, lrs)
            }
          case (In, e, CollectionValue(es)) =>
            val b = es.contains(e)
            BoolValue(b)
          case (Cons, e, CollectionValue(es)) => CollectionValue(e::es)
          case (Snoc, CollectionValue(es), e) => CollectionValue(es:::List(e))
          case _ => throw IError("no case for operator evaluation: " + o.symbol)
        }
    }
  }
  /** partial inverse, for pattern-matching */
  def invert(o: Operator, res: Expression): Option[List[Expression]] = {
    o match {
      case pf: PrefixOperator =>
        ((pf,res)) match {
          case (UMinus,(IntOrRatValue(x,y))) => Some(List(IntOrRatValue(-x,y)))
          case (Not,BoolValue(b)) => Some(List(BoolValue(!b)))
        }
      case inf: InfixOperator =>
        // TODO: only legal for certain collection kinds
        (inf,res) match {
          case (Cons, CollectionValue(e::es)) => Some(List(e,CollectionValue(es)))
          case (Snoc, CollectionValue(es)) if es.nonEmpty => Some(List(CollectionValue(es.init), es.last))
          case _ => None
        }
    }
  }
}