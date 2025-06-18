package info.kwarc.p

// ******* declarations *******

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
  def kind: String // expression, type, ...
  def dfO: Option[Object]
  def defined = dfO.isDefined
  def similar(that: Declaration) = this.kind == that.kind && this.nameO == that.nameO
  def subsumedBy(that: Declaration): Boolean = {
    if (this == that) return true
    (this,that) match {
      case (sc: SymbolDeclaration,sd:SymbolDeclaration) => sc.subsumedBy(sd)
      case (ic: Include, id: Include) => ic.subsumedBy(id)
      case _ => false
    }
  }
}

sealed abstract class NamedDeclaration extends Declaration with Named {
  def label = name
}
sealed abstract class UnnamedDeclaration extends Declaration {
  val nameO = None
}

// ***************** Programs and Declarations **************************************

/** vocabulary + an initial expression to evaluate */
case class Program(voc: TheoryValue, main: Expression) extends SyntaxFragment {
  override def toString = voc.toString + "\n" + main
  def toModule = Module.anonymous(voc.decls)
  def label = "program"
  def children = voc.children ::: List(main)
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
case class Module(name: String, closed: Boolean, df: TheoryValue) extends NamedDeclaration with HasChildren[Declaration] {
  override def toString = {
    val k = if (closed) Keywords.closedModule else Keywords.openModule
    s"$k $name {\n${decls.mkString("\n").indent(2)}}"
  }
  def kind = "theory"
  def decls = df.decls
  def children = decls
  override def childrenInContext = {
    val r = Some(PhysicalTheory(Path(name)))
    decls.map(d => (r, None, d))
  }
  def dfO = Some(df)

  /** for efficient sequential building of declarations: prepends to the last module
   * @param parent the path of the last module (almost redundant, but needed when modules are nested)
   */
  private[p] def addIn(parent: Path, d: Declaration): Module = {
    if (parent.isRoot) copy(df = df.add(d).copyFrom(df)).copyFrom(this)
    else {
      decls.headOption match {
        case Some(m: Module) if m.name == parent.head =>
          val mA = m.addIn(parent.tail, d)
          copy(df = TheoryValue(mA :: decls.tail)).copyFrom(this)
        case _ => throw ASTError("unexpected path")
      }
    }
  }

  /** dereferences a path inside this module, returns the result followed by its ancestors */
  def lookupPathAndParents(path: Path, parents: List[NamedDeclaration]): Option[List[NamedDeclaration]] = path.names match {
    case Nil => Some(this :: parents)
    case hd :: tl =>
      lookupO(hd).flatMap {
        case m: Module => m.lookupPathAndParents(Path(tl), this :: parents)
        case d: NamedDeclaration if tl.isEmpty =>
          Some(d :: parents)
        case _ => None
      }
  }
  def lookupPath(path: Path) = lookupPathAndParents(path, Nil).map(_.head)

  /** like lookupPath but with sharper return type, should also be called on checked paths */
  def lookupModule(path: Path): Option[Module] = lookupPath(path) match {
    case s @ Some(m: Module) => Some(m)
    case _ => None
  }
}

object Module {
  def anonymous(decls: List[Declaration]) = Module("", false, decls)
  def apply(name: String, closed: Boolean, ds: List[Declaration] = Nil): Module = Module(name, closed, TheoryValue(ds))
}

/** parent of all declarations that do not nest other declarations */
sealed trait AtomicDeclaration extends Declaration {
  def tp: Type
  def children = tp :: dfO.toList
}

/** include within a module */
case class Include(dom: Theory, dfO: Option[Expression], realize: Boolean) extends UnnamedDeclaration with AtomicDeclaration {
  def tp = ClassType(dom)
  /** defined/realized includes will/must be total */
  def total = defined || realize
  /** excludes the degenerate case of a defined realization */
  def actualRealize = realize && !defined
  def kind = "include"
  override def toString = {
    val kw = if (actualRealize) "realize" else "include"
    val dfS = dfO match {
      case None | Some(null) => ""
      case Some(d)           => " = " + d.toString
    }
    kw + " " + dom + dfS
  }
  def label = "include"
  def subsumedBy(that: Include): Boolean = {
    this.dom == that.dom && (!this.defined || this.dfO == that.dfO)
  }
}

object Include {
  def apply(dom: Theory, dfO: Option[Expression] = None): Include = Include(dom, dfO, false)
}

/** parent class of all declarations that introduce symbols, e.g., type, function, predicate symbols */
sealed trait SymbolDeclaration extends NamedDeclaration with AtomicDeclaration {
  def tpSep: String // ":", "<", ...
  override def toString = {
    val tpS = if (tp == null || tp == AnyType) "" else " " + tpSep + " " + tp.toString
    val dfOS = dfO match {
      case Some(t) => " = " + t
      case None    => ""
    }
    kind + " " + name + tpS + dfOS
  }
  def toRef = ClosedRef(name)
  def subsumedBy(that: SymbolDeclaration): Boolean = {
    this.kind == that.kind && this.name == that.name && this.tp == that.tp &&
      (!this.defined || this.dfO == that.dfO)
  }
}

/** declares a type symbol
  * @param tp the upper type bound, [AnyType] if unrestricted, null if to be inferred during checking
  */
case class TypeDecl(name: String, tp: Type, dfO: Option[Type]) extends SymbolDeclaration {
  def kind = Keywords.typeDecl
  def tpSep = "<"
}

/** declares a typed symbol
  * @param tp the type, null if to be inferred during checking
  */
case class ExprDecl(name: String, tp: Type, dfO: Option[Expression], mutable: Boolean) extends SymbolDeclaration {
  def kind = if (mutable) Keywords.mutableExprDecl else "const"
  def tpSep = ":"
}

// ***************** Objects **************************************

/** parent of all anonymous objects like types, expressions, formulas, etc. */
sealed abstract class Object extends SyntaxFragment

/** theories */
sealed trait Theory extends Object {
  /* default values that are overriden only in TheoryValue */
  def toValue: TheoryValue = TheoryValue(decls)
  def decls: List[Declaration] = List(Include(this))
  def isEmpty = this == Theory.empty
  /* TODO: Refs to primitive modules should initially be QuasiFlat */
  private[p] var flatness: Theory.Flatness = Theory.NotFlat
  def isFlat = flatness != Theory.NotFlat
}
object Theory {
  def empty = TheoryValue(Nil)
  def apply(ds: List[Declaration], keepFull: Option[Boolean] = None) = {
    val thy = TheoryValue(ds)
    keepFull.foreach {kf => thy.flatness = if (kf) FullyFlat else QuasiFlat}
    thy
  }

  sealed abstract class Flatness
  /** theory is a value containing all its declarations; includes can be ignored */
  case object FullyFlat extends Flatness
  /** theory is a value containing
   *  - all includes (transitively closed)
   *  - all declarations that subsume an included in ways other than just concretizing
   *  Lookup in a quasi-flat theory can be done efficiently as follows:
   *  1) try local declarations
   *  2) try concrete included declarations
   *  3) try abstract included declarations
   *  In particular, a theory is quasi-flat if it is an extension of a single Ref to a theory with a normalized definiens.
   *  See [PhysicalTheory] to match such theories.
   */
  case object QuasiFlat extends Flatness
  /** no invariants guaranteed, default value */
  case object NotFlat extends Flatness
}

/** types */
sealed trait Type extends Object {
  def known = true
  def skipUnknown = this
  def substitute(sub: Substitution) = Substituter(GlobalContext(""), sub, this)
  def <--(ins: Type*) = SimpleFunType(ins.toList, this)

  /** true if this type is definitely finite (in complex cases, this may be false for finite types)
   * only reliable for fully normalized types
   */
  def finite: Boolean
  def power(n: Int) = ProdType.simple(Range(1, n).toList.map(_ => this))
}
object Type {
  private var unknownCounter = -1
  def unknown(gc: GlobalContext = null) = {
    unknownCounter += 1
    val cont = new UnknownTypeContainer(unknownCounter, null)
    UnknownType(gc, cont, if (gc == null) null else gc.visibleLocals.identity)
  }

  val unbounded = AnyType

  /** normalizes what can be done context-freely, in particular removes unknown types */
  def normalize(tp: Type) = IdentityTraverser(tp)(GlobalContext(""), ())
}

/** typed expressions */
sealed trait Expression extends Object {
  def field(dom: Theory, f: String) = OwnedExpr(this, dom, ClosedRef(f))
  def substitute(sub: Substitution) = Substituter(GlobalContext(""), sub, this)
}

// ************************** Common objects ************************

// Some classes dealing with symbol references and scoping are shared between types and expressions

/** reference to a name */
sealed trait Ref extends Expression with Type with Theory {
  override def substitute(s: Substitution) = this // needed due to double-inheritance
}

/** global reference: to a symbol from an open theory */
case class OpenRef(path: Path) extends Ref {
  override def toString = "." + path
  def label = path.toString
  def children = Nil
  def finite = false
}

/** regional reference: to a symbol from an included theory */
case class ClosedRef(n: String) extends Ref {
  def label = n
  def children = Nil
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
  /** the theory of the owner */
  def ownerDom: Theory
  /** the original object */
  def owned: Object
  override def toString = s"$owner{$owned}"
  def label = "owned"
  def children = List(owner, ownerDom, owned)
  override def childrenInContext = List((None, None, owner), (None, None, ownerDom), (Some(ownerDom), None, owned))
}

object OwnedReference {
  def apply(o: Expression, d: Theory, nd: NamedDeclaration): OwnedObject = {
    val n = nd.name
    nd match {
      case _:ExprDecl => OwnedExpr(o,d, ClosedRef(n))
      case _:TypeDecl => OwnedType(o,d, ClosedRef(n))
      case _:Module => OwnedTheory(o,d, ClosedRef(n))
    }
  }
}

/** expressions translated into another regional context
  *
  * If t is ClosedRef(n), this is the usual field access o.n known from OOP. See also [[Expression.field]]
  * By allowing arbitrary terms, we can delay traversing expressions, which might have to duplicate owner.
  */
case class OwnedExpr(owner: Expression, ownerDom: Theory, owned: Expression) extends Expression with OwnedObject

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
case class OwnedType(owner: Expression, ownerDom: Theory, owned: Type) extends Type with OwnedObject {
  def finite = false
}

/** theories translated to another environment
  * - t nested inside d (in which case t extends d): if o: d -> X, then OwnedTheory(o,d,t) is pushout of t along o
  */
case class OwnedTheory(owner: Expression, ownerDom: Theory, owned: Theory) extends Theory with OwnedObject {
  def finite = false
}

/** common parent for quotation */
sealed trait ObjectOver extends Object {
  def scope: Theory
  def obj: Object
  override def toString = s"$scope{$obj}"
  def label = "quote"
  def children = List(scope, obj)
  override def childrenInContext = List((None, None, scope), (Some(scope), None, obj))
}

// ***************** Theories **************************************

/** anonyomous theories, i.e. list of declarations
 *
 * these are the result of theory normalization
 */
case class TheoryValue(override val decls: List[Declaration]) extends Theory with HasChildren[Declaration] {
  override def toString = {
    this match {
      case PhysicalTheory(p, ds) => p.toString + (if (ds.isEmpty) "" else ds.mkString("{", ", ", "}"))
      case _ => decls.mkString("{", ", ", "}")
    }
  }
  def label = "theory"
  def children = decls
  override def toValue = this // only for efficiency

  /** prepend a declaration */
  def add(d: Declaration) = copy(decls = d :: decls)
  override def copyFrom(sf: SyntaxFragment): this.type = {
    super.copyFrom(sf)
    sf match {
      case t: Theory => flatness = t.flatness
      case _ =>
    }
    this
  }

  def sub(that: TheoryValue) = this.decls.forall(c => that.decls.exists(d => c.subsumedBy(d)))
  //def map(f: Declaration => Declaration) = Theory(decls map f)
  /** after checking: all included theories */
  def supers = decls.collect {
    case id: Include => id.dom
  }
  /** after checking: all undefined included theories */
  def base = decls.collect {
    case id: Include if id.dfO.isEmpty => id.dom
  }
  /** after checking: all undefined symbol declarations */
  def undefined = decls.collect {
    case sd: SymbolDeclaration if sd.dfO.isEmpty => sd
  }

  def lookupPath(path: Path): Option[NamedDeclaration] = lookupO(path.head).flatMap {
    case nd: NamedDeclaration if path.isToplevel => Some(nd)
    case m: Module => m.lookupPath(path.tail)
    case _ => throw IError("unexpected path")
  }
}

object PhysicalTheory {
  def apply(p: Path, sds: List[SymbolDeclaration] = Nil): TheoryValue = TheoryValue(Include(OpenRef(p)) :: sds)
  def unapply(thy: Theory) = thy.decls match {
    case Include(OpenRef(p), None, _) :: ds if ds.forall(_.isInstanceOf[SymbolDeclaration]) =>
      Some((p, ds.map(_.asInstanceOf[SymbolDeclaration])))
    case _ => None
  }
}

/** captures the representational redundancy of theories given by t <-> {include t} */
object TheoryAsValue {
  def apply(t: Theory) = t.toValue
  def unapply(t: Theory) = t match {
    case TheoryValue(List(Include(dom,None,_))) => Some(dom)
    case TheoryValue(_) => None
    case _ => Some(t)
  }
}

// ***************** Types **************************************

/** an omitted type that is to be filled in during type inference */
class UnknownTypeContainer(private var id: Int, private[p] var tp: Type) {
  def label = "???" + id
  override def toString = if (known) tp.toString else label
  def known = tp != null && tp.known
}

/** an unknown type that is to be solved during inference
  * see [[Type.unknown]] for its creation
  *
  * All local variables that were visible when the type was created can be free in the solution.
  * This class can be seen as a redex that abstracts over them and is then applied to some arguments.
  * @param originalContext the free variables, initially context in which this type occurred
  * @param container the mutable container of the solved type, initially null
  * @param sub the argument corresponding to the free variables, initially the identity
  */
case class UnknownType(originalContext: GlobalContext, container: UnknownTypeContainer, sub: Substitution) extends Type {
  // overriding to avoid extremely slow recursion into the global context
  override def hashCode() = container.hashCode() + sub.hashCode()
  override def equals(that: Any) = {
    that match {
      case that: UnknownType =>
        this.container == that.container && this.sub == that.sub
      case _ => false
    }
  }
  override def toString = container.toString + (if (sub != null && !sub.isIdentity) "[" + sub + "]"  else "")
  def label = container.label
  def children = if (sub == null) Nil else sub.children
  override def known = container.known
  override def skipUnknown = if (!known) this else container.tp.skipUnknown.substitute(sub)

  /** solves the unknown type
    * pre: if not null, t is relative to u.gc
    */
  private[p] def set(t: Type): Unit = {
    if (known)
      throw IError("type already inferred")
    if (container.tp == null) {
      // println(s"solving $this as $t")
      container.tp = t.skipUnknown
    } else
      container.tp match {
        case u: UnknownType =>
          u.set(t)
        case _ => throw IError("impossible case")
      }
  }

  /** pattern fragment: sub is a renaming of the free variables */
  def isSolvable = !known && sub.inverse.isDefined
  def finite = if (known) skipUnknown.finite else false
}

/** the type of instances of a theory */
case class ClassType(domain: Theory) extends Type {
  override def toString = domain.toString
  def finite = false
  def label = domain.toString
  def children = Nil
}

/** the type of instances of any theory */
object AnyStructure {
  def apply() = ClassType(TheoryValue(Nil))
  def unapply(t: Type) = t match {
    case ClassType(TheoryValue(Nil)) => Some(())
    case _ => None
  }
}

/** type of quotations of terms of a given type from a different environment, e.g., for inductive types, polynomials
  *
  * can be seen as the variant of OwnedType without owner
  */
case class ExprsOver(scope: Theory, tp: Type) extends Type with ObjectOver {
  def obj = tp
  def finite = false
}

/** atomic built-in base types */
sealed abstract class BaseType(name: String) extends Type { self =>
  override def toString = name
  def label = name
  def children = Nil
}
object BaseType {
  val B = BoolType
  val I = IntType
  val F = FloatType
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

/** floating point numbers */
case object FloatType extends BaseType("float") {
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

/** user-declared exceptions */
case object ExceptionType extends Type {
  override def toString = "exn"
  def finite = false
  def label = toString
  def children = Nil
}

/** interval of integers, unbounded if bounds absent, including lower and upper bound if present */
case class IntervalType(lower: Option[Expression], upper: Option[Expression])
    extends Type {
  private def boundString(e: Option[Expression]) =
    e.map(_.toString).getOrElse("")
  override def toString = s"int[${boundString(lower)};${boundString(upper)}]"
  def label = "int"
  def children = lower.toList ::: upper.toList
  def finite = lower.isDefined && upper.isDefined
  def concrete = lower.forall(_.isInstanceOf[IntValue]) && upper.forall(
    _.isInstanceOf[IntValue]
  )
}

// TODO merge all number types into NumberType(kind: NumberKind), add shortcut for Nat
// remove redundant operator types; use first matching type when infering operator types

case class NumberKind(lower: Option[Expression], upper: Option[Expression], fractions: Boolean) {
  def sub(that: NumberKind): Option[Boolean] = {
    if (this.fractions && !that.fractions) return Some(false)
    val l = NumberType.lessEq(that.lower, this.lower, false).getOrElse(return None)
    val r = NumberType.lessEq(this.upper, that.upper, true).getOrElse(return None)
    Some(l && r)
  }
}

object NumberType {
  def apply(nk: NumberKind) = {
    if (nk.lower.isEmpty && nk.upper.isEmpty) {
      if (nk.fractions) RatType else IntType
    } else {
      if (nk.fractions) throw IError("rational interval")
      else IntervalType(nk.lower, nk.upper)
    }
  }
  def unapply(y: Type) = y match {
    case IntType => Some(NumberKind(None, None, false))
    case RatType => Some(NumberKind(None, None, true))
    case IntervalType(lower, upper) => Some(NumberKind(lower, upper, false))
    case _ => None
  }

  /** compares integer values, using None for sign*infinity */
  def lessEq(e: Option[Expression], f: Option[Expression], sign: Boolean) = {
    (e, f) match {
      case (None, None)  => Some(true)
      case (None, Some(_)) => Some(!sign)
      case (Some(_), None) => Some(sign)
      case (Some(IntValue(m)), Some(IntValue(n))) => Some(m <= n)
      case _  => None
    }
  }
}

/** dependent functions
  * Declarations in ins are given in context-order
  */
case class FunType(ins: LocalContext, out: Type) extends Type {
  override def toString = ProdType(ins).toString + " -> " + out
  def label = "->"
  def children = ins.children ::: List(out)
  override def childrenInContext =
    ins.childrenInContext ::: List((None, Some(ins), out))
  def finite = (out :: ins.decls.map(_.tp)).forall(_.finite)
  def simple = ins.decls.forall(_.anonymous)

  /** only valid if this.simple */
  def simpleInputs = Util.reverseMap(ins.decls)(_.tp)
}

object SimpleFunType {
  def apply(ts: List[Type], t: Type) = FunType(LocalContext.make(ts.map(VarDecl.anonymous)), t)
  def unapply(ft: Type): Option[(List[Type],Type)] = ft match {
    case FunType(ins,out) if ins.decls.forall(_.anonymous) => Some((Util.reverseMap(ins.decls)(_.tp), out))
    case _ => None
  }
}

/** dependent sums/tuples
  * Declarations in comps are given in context-order
  */
case class ProdType(comps: LocalContext) extends Type {
  def label = "(...)"
  def children = comps.children
  override def childrenInContext = comps.childrenInContext
  override def toString = {
    val (open, close) =
      if (decls.length == 1 && decls.head.anonymous) ("", "") else ("(", ")")
    val declsS =
      decls.map(vd => if (vd.anonymous) vd.tp.toString else vd.toString)
    declsS.mkString(open, ",", close)
  }
  def decls = comps.decls.reverse
  def finite = decls.forall(_.tp.finite)
  def simple = comps.decls.forall(_.anonymous)

  /** only valid if this.simple */
  def simpleComps = Util.reverseMap(comps.decls)(_.tp)
}
object ProdType {
  def simple(ts: List[Type]) = ProdType(
    LocalContext.make(ts.map(VarDecl.anonymous))
  )
}

/** homogeneous collections, unifies lists, finite sets, options, etc.
  * all types are Curry-subquotients of lists, i.e., there is only one introduction form for all of them
  */
case class CollectionType(elem: Type, kind: CollectionKind) extends Type {
  override def toString = {
    s"$kind[$elem]"
  }
  def label =
    CollectionKind.allKinds.find(_._2 == kind).map(_._1).getOrElse("collection")
  def children = List(elem)
  def finite = kind.norep && elem.finite
}

/**
 * collections (sets, lists, etc.) are represented using the same data structures; this chooses the kind of collection
 * @param norep no repetitions, equivalent to idempotent if commutative
 * @param comm commutative
 * @param sizeOne size <= 1
 */
case class CollectionKind(norep: Boolean, comm: Boolean, sizeOne: Boolean) {
  override def toString = CollectionKind.allKinds.find(_._2 == this).get._1
  def apply(a: Type) = CollectionType(a, this)
  def apply(es: List[Expression]) = CollectionValue(es, this)
  def unapply(a: Type) = a match {
    case CollectionType(e, k) if k == this => Some(e)
    case _ => None
  }
  def unapply(e: Expression) = e match {
    case CollectionValue(es,k) if k == this => Some(es)
    case _ => None
  }
  /** subtyping (with quotients as supertypes, i.e., list <: set) */
  def sub(that: CollectionKind) = {
    this.sizeOne || ((!this.norep || that.norep) && (!this.comm || that.comm))
  }
  /** union of the corresponding types, e.g., set.union(list) == set */
  def union(that: CollectionKind) = {
    if (this.sizeOne) that
    else if (that.sizeOne) this
    else
      CollectionKind(this.norep || that.norep, this.comm || that.comm, false)
  }
  /** intersection of the corresponding types, e.g., set.inter(list) == list */
  def inter(that: CollectionKind) = {
    if (this.sizeOne || that.sizeOne) CollectionKind.Option
    else
      CollectionKind(this.norep && that.norep, this.comm && that.comm, false)
  }
}

/** defines abbreviations for the supported kinds */
object CollectionKind {
  /** repetitions, order */
  val List = CollectionKind(false, false, false)
  /** no repetitions, no ordered */
  val Set = CollectionKind(true, true, false)
  /** repetitions, no order */
  val Bag = CollectionKind(false, true, false)
  /** no repetitions, order */
  val UList = CollectionKind(true, false, false)
  /** size at most 1 (treated as a list to indicate that no normalization is needed even though it is kind of commutative and idempotent) */
  val Option = CollectionKind(false, false, true)
  val allKinds = scala.List(
    "list" -> this.List,
    "ulist" -> this.UList,
    "bag" -> this.Bag,
    "set" -> this.Set,
    "option" -> this.Option
  )
  val allKeywords = allKinds.map(_._1)
}

case class ProofType(formula: Expression) extends Type {
  override def toString = "|- " + formula
  def label = "|-"
  def children = List(formula)
  def finite = true
}

// ***************** Expressions **************************************

// **************************** introduction/elimination forms for built-in types

/** the current instance
  * @param level 1 for 'this' (written as '.'), 2 for surrounding instance (written as '..') and so on
  */
/*
  TODO: replace this with object This
  use Eval(...(Eval(This))...) instead of This(n), parse ..c as Eval(c)
  checking Eval(_) always pops a frame - no need to substitute
  Whether Eval is legal and with which type, depends on the region, e.g., always if transparent, only ExprOver if quoted, never if owned
 */
case class This(level: Int) extends Expression {
  override def toString = if (level <= 0) "illegal" else Range(0,level).map(_ => '.').mkString("")
  def children = Nil
  def label = "this" + toString
}

/** instance of a theory, introduction form for [[ClassType]] */
case class Instance(theory: Theory) extends Expression with MutableExpressionStore {
  override def toString = if (isRuntime) s"instance of $theory" else theory.toString
  def label = "new"
  def children = theory.children
  override def childrenInContext =
    theory.children.map(c => (Some(theory), None, c))

  /** non-null exactly for run-time instances, which additionally carry the current values of all fields */
  private[p] var fields: List[MutableExpression] = null

  /** true if this is a run-time instance, e.g., has been initialized already */
  private[p] def isRuntime = fields != null
}

/** a quoted expressions; introduction form of [[ExprsOver]] */
case class ExprOver(scope: Theory, expr: Expression) extends Expression with ObjectOver {
  def obj = expr
}

/** backquote/evaluation inside a [[ExprsOver]] */
case class Eval(syntax: Expression) extends Expression {
  override def toString = s"`$syntax`"
  def label = "eval"
  def children = List(syntax)
}

object Eval {
  // like Eval, but avoids introduing redex
  def reduced(exp: Expression) = exp match {
    case ExprOver(_, e) => e
    case e => Eval(e)
  }
}

/*
/** runs a Prolog query relative to a theory */
case class Query(scope: Theory, qvars: LocalContext, query: Expression) extends Expression {
  override def toString = s"$scope ?? $query"
}
 */

/** anonymous function, introduction form for [[FunType]]
  * @param mayReturn whether a return statement in the body is caught at this level or passed through
  */
case class Lambda(ins: LocalContext, body: Expression, mayReturn: Boolean) extends Expression {
  /** used at run-time to store the frame relative to which the body must be interpreted when the function is applied */
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
  def label = "lambda"
  def children = ins.children ::: List(body)
  override def childrenInContext = ins.childrenInContext ::: List((None, Some(ins), body))
}

object Lambda {
  /** makes a Lambda returnable */
  def allowReturn(e: Expression) = e match {
    case l:Lambda if !l.mayReturn => l.copy(mayReturn = true).copyFrom(l)
    case _ => e
  }
}

/** function application, elimination form for [[FunType]]
  * arguments are given in left-to-right order, i.e., opposite to the one used in [[FunType]]
  */
case class Application(fun: Expression, args: List[Expression]) extends Expression {
  override def toString = {
    fun match {
      case BaseOperator(o: InfixOperator, _) =>
        args.mkString("(", " " + o.symbol + " ", ")")
      case BaseOperator(o: PrefixOperator, _) => o.symbol + args.mkString
      case _                                  => fun.toString + args.mkString("(", ", ", ")")
    }
  }
  def label = "apply"
  def children = fun :: args
}

/** tuples, introduction form for [[ProdType]]
  * components are given in left-to-right order, i.e., the opposite order of the one in [[ProdType]]
  */
case class Tuple(comps: List[Expression]) extends Expression {
  override def toString = comps.mkString("(", ", ", ")")
  def label = "tuple"
  def children = comps
}

/** projection, elimination form for [[ProdType]]
  * @param index tuple component, starting at 1
  */
case class Projection(tuple: Expression, index: Int) extends Expression {
  override def toString = s"$tuple.$index"
  def label = "proj"
  def children = List(tuple, IntValue(index))
}

/** collections, introduction form for [[CollectionType]] */
case class CollectionValue(elems: List[Expression], kind: CollectionKind) extends Expression {
  override def toString = kind + elems.mkString("[",",","]")
  def label = "collection"
  def children = elems
  /** the elements, normalized according to collection kind */
  def normalize = {
    var es = elems
    if (kind.norep) es = es.distinct
    if (kind.comm) es = es.sortBy(_.hashCode())
    if (es == elems) this else CollectionValue(es,kind)
  }
}

/** list elements access, elimination form for non-commutative [[CollectionType]]s
  * @param position must evaluate to an [[IntValue]] between 0 and length-1; type-checking is undecidable and over-approximates
  */
case class ListElem(list: Expression, position: Expression) extends Expression {
  override def toString = s"$list[$position]"
  def label = "element"
  def children = List(list, position)
}

case class Quantifier(univ: Boolean, vars: LocalContext, body: Expression) extends Expression {
  def label = if (univ) "forall" else "exists"
  override def toString = s"($label $vars.$body)"
  def children = vars.children ::: List(body)
  override def childrenInContext = vars.childrenInContext ::: List((None,Some(vars),body))
}

/** typed equality, possibly negated */
case class Equality(positive: Boolean, tp: Type, left: Expression, right: Expression) extends Expression {
  def label = if (positive) "equal" else "inequal"
  def op = if (positive) "==" else "!="
  override def toString = s"$left $op $right"
  def children = List(tp,left,right)
}
object Equality {
  def reduce(pos: Boolean): Connective = if (pos) And else Or
}

case class Assert(formula: Expression) extends Expression {
  override def toString = "|- " + formula
  def label = "assert"
  def children = List(formula)
}

/** base values, introduction forms of [[BaseType]] */
sealed abstract class BaseValue(val value: Any, val tp: BaseType) extends Expression {
  def label = value.toString + "  :" + tp.toString
  def children = Nil
}

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
case class RatValue(enumer: BigInt, denom: BigInt) extends BaseValue(enumer / denom, RatType) {
  override def toString = enumer.toString + "/" + denom.toString
}

/** helper object to construct/pattern-match numbers such that [[IntType]] is a subtype of [[RatType]] */
object IntOrRatValue {
  def apply(e: BigInt, d: BigInt): BaseValue = {
    val g = e gcd d
    val eg = e / g
    val dg = d / g
    if (dg == 1) IntValue(eg) else RatValue(eg, dg)
  }
  def unapply(e: Expression) = e match {
    case IntValue(i)    => Some((i, BigInt(1)))
    case RatValue(i, j) => Some((i, j))
    case _              => None
  }
}

case class FloatValue(v: Double) extends BaseValue(v, FloatType) {
  override def toString = v.toString
}

object FloatOrRatValue {
  def unapply(e: Expression) = e match {
    case FloatValue(f) => Some(f)
    case IntOrRatValue(e,d) => Some(e.toDouble/d.toDouble)
    case _ => None
  }
}

/** elements of [[StringType]] */
case class StringValue(v: String) extends BaseValue(v, StringType) {
  override def toString = "\"" + String.escape(v) + "\""
}

object String {
  def escape(s: String) = s.replace("\\", "\\\\").replace("\"", "\\\"")
}

/** built-in operators, bundles various elimination forms for the built-in types
  * @param operator the operator
  * @param tp its type (most operators are ad-hoc polymorphic), null if to be infered during checking
  */
case class BaseOperator(operator: Operator, tp: Type) extends Expression {
  override def toString = "(" + operator.symbol + ":" + tp + ")"
  def label = operator.symbol
  def children = Nil
}

/** value that is promised to exist but is not known
  * executing this is an error; but it type-checks against every type
  */
case class UndefinedValue(tp: Type) extends Expression {
  override def toString = "???"
  def label = "???"
  def children = List(tp)
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
    val vlS = dfO match {
      case Some(v) => " = " + v.toString
      case None    => ""
    }
    s"$name$sep $tpS$vlS"
  }
  def label = if (name != "") name else "_"
  def children = tp :: dfO.toList
  def toRef = VarRef(name).copyFrom(this)
  def toSub = VarDecl.sub(name, toRef)
}
object VarDecl {
  def apply(n: String, tp: Type, dfO: Option[Expression] = None, mutable: Boolean = false): VarDecl = VarDecl(n, tp, dfO, mutable, false)
  def anonymous(tp: Type) = VarDecl("", tp)
  def output(tp: Type) = VarDecl("", tp, None, false, true)
  def sub(n: String, df: Expression) = VarDecl(n, null, Some(df))

  class SpecialVarName(key: String) {
    var next = -1
    val prefix = "_" + key + "_"
    val prefixL = prefix.length
    def fresh() = {next += 1; apply(next)}
    def apply(i:Int) = prefix + i.toString
    def unapply(s: String) = if (s.startsWith(prefix)) Some(s.substring(prefixL)) else None
  }
}

/** local reference: to a variable */
case class VarRef(name: String) extends Expression {
  override def toString = name
  def label = name
  def children = Nil
}

/** assignment to mutable local variables */
case class Assign(target: Expression, value: Expression) extends Expression {
  override def toString = s"$target = $value"
  def label = ":="
  def children = List(target, value)
}

/** sequence of expressions, ;-operator
  * evaluates to its last element, variable declarations are in scope till the end of their block
  */
case class Block(exprs: List[Expression]) extends Expression {
  override def toString = exprs.mkString("{", "; ", "}")
  def label = "block"
  def children = exprs
  override def childrenInContext = {
    var ctx = LocalContext.empty
    exprs.map { e =>
      val c = (None, Some(ctx), e)
      ctx = ctx.append(LocalContext.collectContext(e))
      c
    }
  }
}

/** if-then-else, ternary operators, can be seen as elimination form of [[BoolType]] */
case class IfThenElse(cond: Expression, thn: Expression, els: Option[Expression]) extends Expression {
  override def toString = {
    val elsS = els.map(e => " else " + e).getOrElse("")
    s"if $cond $thn$elsS"
  }
  def label = "if"
  def children = cond :: thn :: els.toList
}

/** unifies pattern-matching and exception handling */
case class Match(expr: Expression, cases: List[MatchCase], handler: Boolean) extends Expression {
  def label = if (handler) "handle" else "match"
  override def toString = expr.toString + " " + label + " {\n" + cases.mkString("\n") + "\n}"
  def children = expr :: cases
}

/** case in a match: context |- pattern -> body */
case class MatchCase(context: LocalContext, pattern: Expression, body: Expression) extends Expression {
  override def toString = pattern.toString + " -> " + body
  def label = "case"
  def children = List(context, pattern, body)
  override def childrenInContext =
    (None, None, context) :: List(pattern, body).map(e =>
      (None, Some(context), e)
    )
}

/** for-loop, can be seen as elimination form of [[CollectionType]], behaves like map
  * @param range must evaluate to list
  */
case class For(vd: VarDecl, range: Expression, body: Expression) extends Expression {
  override def toString = s"for (${vd.name} in $range) $body"
  def label = "for"
  def children = List(vd, range, body)
  override def childrenInContext =
    cf(vd, range) ::: List((None, Some(LocalContext(vd)), body))
}

/** while-loop */
case class While(cond: Expression, body: Expression) extends Expression {
  override def toString = s"while $cond $body"
  def label = "while"
  def children = List(cond, body)
}

/** unifies return and throw statements */
case class Return(exp: Expression, thrw: Boolean) extends Expression {
  def label = if (thrw) "throw" else "return"
  override def toString = {
    label + " " + exp
  }
  def children = List(exp)
}

// *********************************** Operators *****************************

/** parent class of all operators
  *
  * Operators carry concrete syntax and typing information so that their processing is controlled by the operator,
  * not by the parser/checker/printer.
  * For the latter to be able to access this information, all operators must be listed in the companion object [[Operator]]
  */
sealed abstract class Operator(val symbol: String) {
  val length = symbol.length
  def types: List[FunType]
  def polyTypes(u: UnknownType): List[FunType] = Nil
  def uniqueType: Option[Type] = None
  def makeExpr(args: List[Expression]) = Application(BaseOperator(this, uniqueType.getOrElse(Type.unknown(null))), args)
  def invertible: Boolean
  def isCheckable = !isDynamic && !isPseudo
  def isDynamic = false
  def isPseudo = false
}

/** operators with binary infix notation (flexary flag not supported yet) */
sealed abstract class InfixOperator(s: String, val precedence: Int, val assoc: Associativity = NotAssociative) extends Operator(s) {
  def apply(l: Expression, r: Expression) = makeExpr(List(l, r))
  def unapply(e: Expression) = e match {
    case Application(BaseOperator(op,_), List(l,r)) if op == this => Some((l,r))
    case _ => None
  }
  def invertible = false
  def rightAssociative = assoc == RightAssociative
  def associative = assoc match {
    case Semigroup | Monoid(_) => true
    case _ => false
  }
  def neutral = assoc match {
    case Monoid(n) => Some(n)
    case _ => None
  }
}

abstract class Associativity
case object NotAssociative extends Associativity
case object Semigroup extends Associativity
case class Monoid(neut: Expression) extends Associativity
case object RightAssociative extends Associativity

/** operators with prefix notation */
sealed abstract class PrefixOperator(s: String) extends Operator(s) {
  def apply(e: Expression) = makeExpr(List(e))
  def invertible = true
}

// for type abbreviations
import BaseType._

/** arithmetic operators */
sealed trait Arithmetic {
  val types = List(I <-- (I, I), R <-- (R, R), R <-- (I, R), R <-- (R, I), F <-- (F,F))
}

/** boolean connectives */
sealed trait Connective extends Operator {
  def apply(args: List[Expression]): Expression
  def tp = B <-- (B, B)
  val types = List(tp)
  override val uniqueType = Some(tp)
  def toBaseOperator = BaseOperator(this,tp)
}

/** comparison operators for base values */
sealed trait Comparison {
  val types = List(B <-- (I, I), B <-- (R, R), B <-- (I, R), B <-- (R, I), B <-- (S, S), B <-- (B, B))
}

case object Plus extends InfixOperator("+", 0, Semigroup) with Arithmetic {
  override val types = (S<--(S,S)) :: Times.types
  override def polyTypes(u: UnknownType) = List(L(u)<--(L(u),L(u)))
  override def associative = true
}
case object Minus extends InfixOperator("-", 0) with Arithmetic
case object Times extends InfixOperator("*", 10, Monoid(IntValue(1))) with Arithmetic
case object Divide extends InfixOperator("/", 10) {
  val types = List(R<--(I,I), R<--(R,R), R<--(I,R), R<--(R,I), F<--(F,F))
}
case object Minimum extends InfixOperator("min", 10, Semigroup) with Arithmetic
case object Maximum extends InfixOperator("max", 10, Semigroup) with Arithmetic

case object Power extends InfixOperator("^", 20, RightAssociative) {
  val types = List(R<--(I,I), R<--(R,R), R<--(I,R), R<--(R,I), F<--(F,R))
}

case object In extends InfixOperator("in", -10) {
  val types = Nil
  override def polyTypes(u: UnknownType) = List(BoolType <-- (u, CollectionKind.Set(u)), BoolType <-- (u, CollectionKind.List(u)))
}

case object Cons extends InfixOperator("-:", -10, RightAssociative) {
  val types = Nil
  override def polyTypes(u: UnknownType) = List(L(u) <-- (u, L(u)))
  override def invertible = true
}

case object Snoc extends InfixOperator(":-", -10) {
  val types = Nil
  override def polyTypes(u: UnknownType) = List(L(u) <-- (L(u), u))
  override def invertible = true
}

case object And extends InfixOperator("&", -20, Monoid(BoolValue(true))) with Connective {
  def apply(args: List[Expression]): Expression = args match {
    case Nil      => BoolValue(true)
    case e :: Nil => e
    case hd :: tl => apply(hd, apply(tl))
  }
  override def isDynamic = true
}
case object Or extends InfixOperator("|", -20, Monoid(BoolValue(false))) with Connective {
  def apply(args: List[Expression]): Expression = args match {
    case Nil      => BoolValue(false)
    case e :: Nil => e
    case hd :: tl => apply(hd, apply(tl))
  }
}

/** implication a => b is the same as comparision a <= b; but we need a separate operator to get the right notation */
case object Implies extends InfixOperator("=>", -20, RightAssociative) with Connective {
  def apply(args: List[Expression]): Expression = args match {
    case Nil      => BoolValue(false)
    case e :: Nil => e
    case _ => Implies(And(args.init), args.last)
  }
  override def isDynamic = true
}

case object Less extends InfixOperator("<", -10) with Comparison
case object LessEq extends InfixOperator("<=", -10) with Comparison
case object Greater extends InfixOperator(">", -10) with Comparison
case object GreaterEq extends InfixOperator(">=", -10) with Comparison

case object UMinus extends PrefixOperator("-") {
  val types = List(I <-- I, R <-- R)
}
case object Not extends PrefixOperator("!") {
  val types = List(B <-- B)
}

trait PseudoOperator extends Operator {
  override def isPseudo = true
  def types = Nil
}

case object Equal extends InfixOperator("==", -10) with PseudoOperator
case object Inequal extends InfixOperator("!=", -10) with PseudoOperator

object Operator {
    val infixes = List(
      Plus, Minus, Times, Divide, Power,
      Minimum, Maximum,
      And, Or, Implies,
      Less, LessEq, Greater, GreaterEq,
      In, Cons, Snoc,
      Equal, Inequal
    )
    val prefixes = List(UMinus, Not)

    def simplify(bo: BaseOperator, as: List[Expression]): Expression = {
      val o = bo.operator
      val numArgs = as.length
      def failNumArgs = throw IError(o + " applied to " + numArgs + " arguments")
      o match {
        case pf: PrefixOperator =>
          if (numArgs != 1) failNumArgs
          ((pf, as.head)) match {
            case (UMinus, (IntOrRatValue(x, y))) => IntOrRatValue(-x, y)
            case (Not, BoolValue(b)) => BoolValue(!b)
            case _ => throw IError("missing case for " + pf)
          }
        case inf: InfixOperator =>
          if (numArgs != 2) {
            if (inf.associative) {
              if (numArgs == 0) inf.neutral getOrElse failNumArgs
              else if (numArgs == 1) as(0)
              else simplify(bo, List(as.head, simplify(bo,as.tail)))
            } else {
              failNumArgs
            }
          } else (inf, as(0), as(1)) match {
            case (Plus, IntOrRatValue(u, v), IntOrRatValue(x, y)) =>
              IntOrRatValue(u * y + v * x, v * y)
            case (Minus, IntOrRatValue(u, v), IntOrRatValue(x, y)) =>
              IntOrRatValue(u * y - v * x, v * y)
            case (Times, IntOrRatValue(u, v), IntOrRatValue(x, y)) =>
              IntOrRatValue(u * x, v * y)
            case (Minimum, IntOrRatValue(u, v), IntOrRatValue(x, y)) =>
              IntOrRatValue((u * y) min (v * x), v * y)
            case (Maximum, IntOrRatValue(u, v), IntOrRatValue(x, y)) =>
              IntOrRatValue((u * y) max (v * x), v * y)
            case (Divide, IntOrRatValue(u, v), IntOrRatValue(x, y)) =>
              if (x == 0) throw ASTError("division by 0")
              else IntOrRatValue(u * y, v * x)
            case (c: Comparison, IntOrRatValue(u, v), IntOrRatValue(x, y)) =>
              val d = u * y - v * x
              val s = if (d > 0) 1 else if (d < 0) -1 else 0
              (s, c) match {
                case (-1, Less | LessEq) | (1, Greater | GreaterEq) | (0, LessEq | GreaterEq) => BoolValue(true)
                case _ => BoolValue(false)
              }
            case (c: Comparison, BoolValue(l), BoolValue(r)) =>
              val b = c match {
                case Less => !l && r
                case LessEq => !l || r
                case Greater => l && !r
                case GreaterEq => l || !r
              }
              BoolValue(b)
            case (Plus, FloatValue(f), FloatValue(g)) => FloatValue(f+g)
            case (Minus, FloatOrRatValue(f), FloatOrRatValue(g)) => FloatValue(f-g)
            case (Times, FloatOrRatValue(f), FloatOrRatValue(g)) => FloatValue(f*g)
            case (Divide, FloatOrRatValue(f), FloatOrRatValue(g)) => FloatValue(f/g)
            case (Power, FloatOrRatValue(f), FloatOrRatValue(g)) => FloatValue(Math.pow(f,g))
            case (And, BoolValue(l), BoolValue(r)) => BoolValue(l && r)
            case (Implies, BoolValue(l), BoolValue(r)) => BoolValue(if (l) r else true)
            case (Or, BoolValue(l), BoolValue(r)) => BoolValue(l || r)
            case (Plus, StringValue(l), StringValue(r)) => StringValue(l + r)
            case (Plus, CollectionValue(l,lk), CollectionValue(r,rk)) =>
              CollectionValue(l ::: r, lk.union(rk))
            case (In, e, CollectionValue(es,_)) =>
              val b = es.contains(e)
              BoolValue(b)
            case (Cons, e, CollectionValue(es,k)) => CollectionValue(e :: es, k.copy(sizeOne=false))
            case (Snoc, CollectionValue(es,k), e) => CollectionValue(es ::: List(e), k.copy(sizeOne=false))
            case _ => throw IError("no case for operator evaluation: " + o.symbol)
          }
        case _: PseudoOperator => throw IError("unealborated pseudo-operator")
      }
    }

    /** partial inverse, for pattern-matching */
    def invert(o: Operator, res: Expression): Option[List[Expression]] = {
      o match {
        case pf: PrefixOperator =>
          ((pf, res)) match {
            case (UMinus, (IntOrRatValue(x, y))) =>
              Some(List(IntOrRatValue(-x, y)))
            case (Not, BoolValue(b)) => Some(List(BoolValue(!b)))
            case _ => throw IError("operator not invertible: " + pf)
          }
        case inf: InfixOperator =>
          (inf, res) match {
            case (Cons, CollectionValue(e :: es, k)) if !k.comm =>
              Some(List(e, CollectionValue(es, k)))
            case (Snoc, CollectionValue(es, k)) if es.nonEmpty && !k.comm =>
              Some(List(CollectionValue(es.init, k), es.last))
            case _ => None
          }
        case _: PseudoOperator => None
      }
    }
}
