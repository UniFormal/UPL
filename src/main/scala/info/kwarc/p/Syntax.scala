package info.kwarc.p

/**** TODO
 * every declaration in a module can be open (= static) or closed (dynamic); hack with global flag can be undone
 * the open/close flag of a module only defines the default
 * static methods may be abstract
 * static methods are inherited, i.e., kept during normalization
 * static methods are accessed using global references, thus not affected by ownership/quotation, dereferencing uses a different method
 * intro forms (e.g., for list making or monad return) are magic static methods that are found via the expected type
 *
 * every declaration in a module can be input or output
 * regional input = parameters
 * global input = environment variables etc.
 */


// ******* declarations *******

/** parent of all structuring classes like module, symbol declarations */
sealed abstract class Declaration extends SyntaxFragment with MaybeNamed {
  private[p] var subsumed = false // can be used to mark that this is redundant due to a later more specific one
  private[p] var subsuming = false // can be used to mark that this makes a previous declarations redundant
  override def copyFrom(sf: SyntaxFragment): this.type = {
    super.copyFrom(sf)
    sf match {
      case d: Declaration =>
        subsuming = d.subsuming
        subsumed = d.subsumed
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
  def modifiers: Modifiers
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
  def modifiers = Modifiers(closed, false)
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
  def ntO: Option[Notation]
  def modifiers: Modifiers
  def subsumedBy(that: SymbolDeclaration): Boolean = {
    this.kind == that.kind && this.name == that.name && this.tp == that.tp &&
      (!this.defined || this.dfO == that.dfO) &&
      modifiers == that.modifiers
  }
}

/** unifies ExprDecl and VarDecl */
trait TypedDeclaration extends Named {
  def tp: Type
}

/** modifiers of declarations; not every modifiers is legal for every declaration */
case class Modifiers(closed: Boolean, mutable: Boolean) {
  override def toString = (if (closed) Keywords.closedDecl else Keywords.openDecl) + " " +
    (if (mutable) Keywords.mutableExprDecl + " " else "")
}

/** declares a type symbol
  * @param tp the upper type bound, [AnyType] if unrestricted, null if to be inferred during checking
  * @param args input (bound in both type bound and definition)
  */
case class TypeDecl(name: String, tp: Type, dfO: Option[Type], modifiers: Modifiers) extends SymbolDeclaration {
  def kind = Keywords.typeDecl
  def tpSep = "<"
  def ntO = None
}

/** declares a typed symbol
  * @param tp the type, null if to be inferred during checking
  */
case class ExprDecl(name: String, tp: Type, dfO: Option[Expression], ntO: Option[Notation], modifiers: Modifiers) extends SymbolDeclaration with TypedDeclaration {
  def kind = if (modifiers.mutable) Keywords.mutableExprDecl else Keywords.exprDecl
  def tpSep = ":"
}

// ***************** Objects **************************************

/** parent of all anonymous objects like types, expressions, formulas, etc. */
sealed abstract class Object extends SyntaxFragment

/** theories */
sealed trait Theory extends Object {
  /* default values that are overridden only in TheoryValue */
  def toValue: TheoryValue = TheoryValue(decls)
  def decls: List[Declaration] = List(Include(this))
  def isEmpty = this == Theory.empty
  def sub(that: Theory) = this.decls.forall(that.decls.contains)
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
  override def toString = n
  def label = n
  def children = Nil
  def finite = false
}

/** local reference: to a variable */
case class VarRef(name: String) extends Ref {
  override def toString = name
  def label = name
  def children = Nil
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
  def add(ds: List[Declaration]) = copy(decls = ds ::: decls)

  // def slowAppend(ds: List[Declaration]) = copy(decls = decls ::: ds)
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

object TheoryValue {
  def apply(decls: Declaration*): TheoryValue = TheoryValue(decls.toList)
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
  * @param container the mutable container of the solved type, initially empty
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
  override def skipUnknown = if (!known) this else {
    val sk = container.tp.skipUnknown
    if (sub == null)
      sk // only happens if unchecked content is reused after checking has solved a type
    else
      sk.substitute(sub)
  }

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
sealed abstract class BaseType extends Type {
  def name: String
  override def toString = name
  def label = name
  def children = Nil
}

object BaseType {
  val B = BoolType
  val N = NumberType.Nat
  val I = NumberType.Int
  val R = NumberType.Rat
  val F = NumberType.Float
  val S = StringType
  def L(e: Type) = CollectionKind.List(e)
  def O(e: Type) = CollectionKind.Option(e)
}

/** 0 elements */
case object EmptyType extends BaseType {
  val name = "empty"
  def finite = true
}

/** 1 element */
case object UnitType extends BaseType {
  val name = "unit"
  def finite = true
}

/** 2 elements */
case object BoolType extends BaseType {
  val name = "bool"
  def finite = true
}

/** strings (exactly as implemented by Scala) */
case object StringType extends BaseType {
  val name = "string"
  def finite = false
}

/** universal type of all expressions */
case object AnyType extends BaseType {
  val name = "any"
  def finite = false
}

/** user-declared exceptions */
case object ExceptionType extends Type {
  override def toString = "exn"
  def finite = false
  def label = toString
  def children = Nil
}

/**
 * all numbers are represented in the same way using subtypes for specific number kinds
 * @param negative negative numbers allowed
 * @param fractional fractions, i.e., non-one denominator, allowed
 * @param imaginary imaginary numbers, i.e., non-zero imaginary part, allowed
 * @param approximate approximate values (represented as double precision floating point) allowed
 * @param infinite real or (if allowed) imaginary part may positive or (if allowed) negative infinity
 */
case class NumberType(negative: Boolean, fractional: Boolean, imaginary: Boolean, approximate: Boolean, infinite: Boolean)
  extends BaseType {
  def name = {
    NumberType.parseTable.find(_._2 == this) match {
      case Some((s,_)) => s
      case _ =>
        var num = NumberType.parseTable.find(_._2 == NumberType(negative,fractional,false,false,false)).get._1
        if (imaginary) num += "C"
        if (approximate) num += "F"
        if (infinite) num += "I"
        num
    }
  }
  def finite = false
  def flagMap(that: NumberType)(f: (Boolean,Boolean) => Boolean) = (
    f(negative, that.negative), f(fractional, that.fractional), f(imaginary, that.imaginary),
    f(approximate, that.approximate), f(infinite,that.infinite)
  )
  def sub(that: NumberType): Boolean = {
    flagMap(that)({case (x,y) => !x || y}).productIterator.forall(_ == true)
  }
  def union(that: NumberType) = {
    val fs = flagMap(that)(_ || _)
    NumberType(fs._1, fs._2, fs._3, fs._4, fs._5)
  }
  def inter(that: NumberType) = {
    val fs = flagMap(that)(_ && _)
    NumberType(fs._1, fs._2, fs._3, fs._4, fs._5)
  }
}
object NumberType {
  def apply(n: Boolean, f: Boolean, im: Boolean): NumberType = NumberType(n,f,im,false,false)
  /** N */
  val Nat = NumberType(false,false,false)
  /** Z */
  val Int = NumberType(true,false,false)
  /** positive rationals (including 0) */
  val PRat = NumberType(false,true,false)
  /** Q */
  val Rat = NumberType(true,true,false)
  /** N+Ni */
  val NatComp = NumberType(false,false,true)
  /** Z+Zi */
  val IntComp = NumberType(true,false,true)
  /** real and imaginary part are positive and rational (including 0) */
  val PRatComp = NumberType(false,true,true)
  /** C, actually Q+Qi */
  val RatComp = NumberType(true,true,true)
  /** floats, i.e., approximate real numbers with infinity */
  val Float = NumberType(true,true,false,true,true)

  /** all types with special string rendering */
  val parseTable = List("nat" -> Nat, "int" -> Int, "rat" -> Rat, "prat" -> PRat, "comp" -> RatComp, "float" -> Float)
  val all = parseTable.map(_._1)
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
  def concrete = lower.forall(_.isInstanceOf[NumberValue]) && upper.forall(
    _.isInstanceOf[NumberValue]
  )
}

object IntervalType {
  //, boundMerge(lower,that.lower, true, true), boundMerge(upper,that.upper, false, true)
  //, boundMerge(lower,that.lower, true, false), boundMerge(upper,that.upper, false, false)
  def boundMerge(l: Option[Expression], r: Option[Expression], lower: Boolean, union: Boolean) = (l,r) match {
    case (None,_) | (_,None) => if (union) None else l orElse r
    case (Some(i),Some(j)) => if (lower) Some(Minimum(i,j)) else Some(Maximum(i,j))
  }

  /** compares integer expressions, using None for sign*infinity */
  def lessEq(e: Option[Expression], f: Option[Expression], sign: Boolean) = {
    (e, f) match {
      case (None, None)  => Some(true)
      case (None, Some(_)) => Some(!sign)
      case (Some(_), None) => Some(sign)
      case (Some(m:NumberValue), Some(n:NumberValue)) => Some(m lessEq n)
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
  def children = List(tuple, NumberValue(index))
}

/** collections, introduction form for [[CollectionType]] */
case class CollectionValue(elems: List[Expression], kind: CollectionKind) extends Expression {
  override def toString = kind.toString + elems.mkString("[",",","]")
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
object Quantifier {
  def optional(u: Boolean, vs: LocalContext, bd: Expression) = if (vs.empty) bd else Quantifier(u,vs,bd)
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

/*
case class Using(hints: List[Expression]) extends Expression {
  override def toString = "using " + hints.mkString(", ")
  def label = "using"
  def children = hints
}

case class ProofElim(elim: Expression, cases: List[List[VarDecl]]) extends Expression
*/

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

case class NumberValue(override val tp: NumberType, re: Real, im: Real) extends BaseValue((re,im), tp) {
  override def toString = {
    val n = normalize
    if (real) re.toString else s"$re+i$im"
  }
  def valid = re.valid && im.valid
  def normal = re.normal && im.normal
  def normalize = if (normal) this else NumberValue(tp, re.normalize, im.normalize)
  def zero = re.zero && im.zero
  def positive = re.positive && im.positive
  def integer = re.integer && im.integer
  def real = im.zero
  def negate = NumberValue(tp.copy(negative = true), re.negate, im.negate)
  def conjugate = NumberValue(tp.copy(negative = true), re, im.negate)
  def invert = conjugate scale ((re times re) plus (im times im)).invert
  def plus(z: NumberValue) = NumberValue(tp union z.tp, re plus z.re, im plus z.im)
  def minus(z: NumberValue) = plus(z.negate)
  def times(z: NumberValue) = NumberValue(tp union z.tp, (re times z.re) minus (im times z.im), (re times z.im) plus (im times z.re))
  def scale(r: Real) = NumberValue(tp union r.tp, re times r, im times r)
  def divide(z: NumberValue) = times(z.invert)
  def lessEq(z: NumberValue) = (re lessEq z.re) && (im lessEq z.im)
  def min(z: NumberValue) = NumberValue(tp union z.tp, re min z.re, im min z.im)
  def max(z: NumberValue) = NumberValue(tp union z.tp, re max z.re, im max z.im)
}

object NumberValue {
  def apply(i: BigInt, j: BigInt = Real.b1): NumberValue = {
    val r = Rat(i,j)
    NumberValue(r.tp, r, Real.zero)
  }
  def zero = NumberValue(NumberType.Nat, Real.zero, Real.zero)
  def one = NumberValue(NumberType.Nat, Real.one, Real.zero)
}

// (un)apply for common special cases
object RealValue {
  def apply(r: Real) = NumberValue(r.tp, r, Real.zero)
  def unapply(e: Expression) = e match {
    case NumberValue(_,r,s) if s == Real.zero => Some(r)
    case _ => None
  }
}
object RatValue {
  def apply(i: BigInt, j: BigInt) = RealValue(Rat(i,j))
  def unapply(e: Expression) = e match {
    case RealValue(Rat(i,j)) => Some((i,j))
    case _ => None
  }
}
object IntValue {
  def apply(i: BigInt) = RatValue(i,1)
  def unapply(e: Expression) = e match {
    case RatValue(i,j) if i % j == 0 => Some(i/j)
    case _ => None
  }
}
object FloatValue {
  def apply(f: Double) = RealValue(ApproxReal(f))
  def unapply(e: Expression) = e match {
    case RealValue(ApproxReal(f)) => Some(f)
    case _ => None
  }
}


sealed abstract class Real {
  def tp: NumberType
  def normal: Boolean
  def valid: Boolean
  def normalize: Real
  def approx: ApproxReal
  def negate: Real
  def invert: Real
  def plus(r: Real): Real
  def minus(r: Real) = plus(r.negate)
  def times(r: Real): Real
  def div(r: Real) = times(r.invert)
  def power(z: Real): Real
  def eq(r: Real): Boolean
  def lessEq(r: Real) = eq(r) || minus(r).negative
  def min(r: Real) = if (lessEq(r)) this else r
  def max(r: Real) = if (lessEq(r)) r else this

  def infinite: Boolean
  def zero: Boolean
  def negative: Boolean
  def positive = !zero && !negative
  def integer: Boolean
  def natural: Boolean
}
object Real {
  val b0 = BigInt(0)
  val b1 = BigInt(1)
  val zero = Rat(b0,b1)
  val one = Rat(b1,b1)
}
case class ApproxReal(value: Double) extends Real {
  override def toString = value.toString
  def tp = NumberType.Float
  def valid = true
  def normal = true
  def normalize = this
  def approx = this
  def negate = ApproxReal(-value)
  def invert = ApproxReal(1/value)
  def plus(r: Real) = ApproxReal(value + r.approx.value)
  def times(r: Real) = ApproxReal(value * r.approx.value)
  def power(r: Real) = ApproxReal(Math.pow(value, r.approx.value))
  def eq(r: Real) = value == r.approx.value

  def zero = value == 0.0
  def infinite = value.isInfinite
  def negative = value < 0
  def integer = false
  def natural = false
}
case class Rat(enu: BigInt, deno: BigInt) extends Real {
  override def toString = {
    val n = normalize
    if (n.integer) n.enu.toString else s"${n.enu}/${n.deno}"
  }
  def tp = NumberType(true, !integer, false, false, infinite) // TODO inferring Nat is often too narrow and breaks type inference later
  def approx = ApproxReal(enu.toDouble/deno.toDouble)
  val valid = deno > 0
  private[p] var _normal = false
  def normal = _normal
  def normalize: Rat = {
    if (deno == 0) return Rat(enu.sign,0)
    if (normal) return this
    val g = enu gcd deno
    val eg = enu / g
    val dg = deno / g
    val r = if (dg < 0) Rat(-eg, -dg) else Rat(eg, dg)
    r._normal = true
    r
  }
  def negate = Rat(-enu,deno)
  def invert = Rat(deno,enu)
  def plus(r: Real) = r match {
    case r: Rat => Rat(enu * r.deno + r.enu * deno, deno * r.deno)
    case _ => approx plus r
  }
  def times(r: Real) = r match {
    case r: Rat => Rat(enu * r.enu, deno * r.deno)
    case _ => approx times r
  }
  def power(r: Real) = r match {
    case r: Rat if r.integer =>
      val n = r.normalize.enu.abs
      val p = Rat(enu pow n.toInt, deno pow n.toInt)
      if (r.negative) p.invert else p
    case _ => approx power r
  }
  def eq(r: Real) = r match {
    case r: Rat => enu * r.deno == r.enu * deno
    case _ => approx eq r
  }
  def zero = enu == 0 && deno != 0
  def infinite = deno == 0
  def negative = (enu > 0 && deno < 0) || (enu < 0 && deno > 0)
  def integer = normalize.deno == 1
  def natural = integer && !negative
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
case class VarDecl(name: String, tp: Type, dfO: Option[Expression], mutable: Boolean, output: Boolean) extends Expression with TypedDeclaration {
  def defined = dfO.isDefined
  def keyword = if (mutable) Keywords.mutableVarDecl else Keywords.varDecl
  override def toString = {
    val sep = if (output) "#" else ":"
    val tpS = if (tp == null) "???" else tp.toString
    val vlS = dfO match {
      case Some(v) => " = " + v.toString
      case None    => ""
    }
    s"$keyword $name$sep $tpS$vlS"
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

abstract class InferenceCallbacks {
  def union(ts: List[Type]): Type
  def unknown(): Type
}

/** parent class of all operators
  *
  * Operators carry concrete syntax and typing information so that their processing is controlled by the operator,
  * not by the parser/checker/printer.
  * For the latter to be able to access this information, all operators must be listed in the companion object [[Operator]]
  */
sealed abstract class Operator {
  val symbol: String
  val length = symbol.length
  /** if this is overridden, type-checking first checks the number of arguments */
  def arity: Option[Int] = None
  /** if the operator has exactly one type, this should be overridden for easy type inference */
  def uniqueType: Option[FunType] = None
  /** if the operator is ad hoc polymorphic, this should be overridden to infer the operator type
   * @param ins the argument types
   * @param union: a callback to compute the union of some types
   * @return the operator type if unique inference possible
   * This function itself does not type-check or solve any unknowns.
   * It just disambiguates what the operator type should be.
   * The type checker then uses the disambiguated type to type-check the arguments, and that may also solve unknowns.
   */
  def typeFor(ins: List[Type], out: Type, cbs: InferenceCallbacks): Option[FunType] = uniqueType
  def makeExpr(args: List[Expression]) = Application(BaseOperator(this, uniqueType.getOrElse(Type.unknown(null))), args)
  def invertible: Boolean
  def isolatableArguments: List[Int] = Nil
  def isolate(pos: Int, args: List[Expression], result: Expression): Option[(Expression,Expression)] = None
  def isCheckable = !isDynamic && !isPseudo
  def isDynamic = false
  def isPseudo = false
}

/** operators that must be defined through magic functions */
sealed trait PseudoOperator extends Operator {
  override def isPseudo = true
  def fixity: Fixity
  def magicName: String
  def types = Nil
  def invertible = false
}

sealed trait GeneralInfixOperator extends Operator {
  val symbol: String
  override def arity = Some(2)
  def precedence: Int
  def assoc: Associativity
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
class PseudoInfixOperator(val symbol: String) extends PseudoOperator with GeneralInfixOperator {
  override def toString = magicName
  def fixity = Infix
  def magicName = "_infix_" + symbol
  def precedence = 0
  def assoc = NotAssociative
}

/** symbol expr */
class PseudoPrefixOperator(val symbol: String) extends PseudoOperator {
  override def toString = magicName
  def fixity = Prefix
  def magicName = "_prefix_" + symbol
}

/** expr symbol */
class PseudoPostfixOperator(val symbol: String) extends PseudoOperator {
  override def toString = magicName
  def fixity = Postfix
  def magicName = "_postfix_" + symbol
}

/** bracketing: comma-separated expressions enclosed in symbol and its mirror image */
class PseudoCircumfixOperator(val symbol: String) extends PseudoOperator {
  def open = symbol
  def close: String = symbol.map(c => Parsable.circumfixClose(c).getOrElse(c)).reverse
  def fixity = Circumfix
  def magicName = "_circumfix_" + open + "_" + close
}

/** binding: symbol bindings . body */
class PseudoBindfixOperator(val symbol: String) extends PseudoOperator {
  override def toString = magicName
  def fixity = Bindfix
  def magicName = "_bindfix_" + symbol
}

object Parsable {
  val symbols = List(Character.CURRENCY_SYMBOL, Character.MATH_SYMBOL, Character.DASH_PUNCTUATION, Character.OTHER_SYMBOL)
  def isInfixChar(c: Char) = (symbols contains c.getType) || (c.getType == Character.OTHER_PUNCTUATION && !"\"';:,.".contains(c))
  def isPrefixChar(c: Char) = isInfixChar(c)
  // right-pointing tacks and similar, not used yet, but could be used for precedences
  def isTurnstileLike(c: Char) = {
    c == 0x22A2 || (c >= 0x22A6 && c <= 0x22AF) || c == 0x2AE2 || c == 0x2AE6 || c == 0x27DD
  }

  /** the matching closing bracket, if any
   *
   *  '‚' and '„' are open punctuation without corresponding closing punctuation
   *  some horizontal brackets have partners that are their vertical mirrors
   *  '[' and '{' have legacy codepoints
   *  square brackets with ticks in corners (0x298D-0x2990) have their mirror images in the wrong order
   *  all other open punctuation has the closing mirror image right afterwards
   */
  def circumfixClose(c: Char): Option[Char] = {
    if (c.getType != Character.START_PUNCTUATION || !c.isMirrored) None
    else if (c == '[') Some(']')
    else if (c == '{') Some('}')
    else if (c == 0x298D) Some(0x2990)
    else if (c == 0x298F) Some(0x298E)
    else Some((c+1).toChar)
  }
  def isCircumfixStart(c: Char) = circumfixClose(c).isDefined
  def isCircumfixChar(c: Char) = isInfixChar(c) || isCircumfixStart(c)

  /** binder symbols cannot be defined based on Unicode classes
   *  we take all symbols called "N-Ary" in their Unicode name plus the quantifiers */
  val bindChars =
    // n-ary
    List(0x2140,0x220F,0x2210,0x2211,0x22C0,0x22C1,0x22C2,0x22C3,0x2A00,0x2A01,0x2A02,0x2A03,0x2A04,0x2A05,0x2A06,0x2A09,0x2AFF) :::
    // quantifiers
    List(0x2200,0x2203,0x2204)
  def isBindfixStart(c: Char) = bindChars contains c
  def isBindfixChar(c: Char) = isInfixChar(c) || isBindfixStart(c)
}

/** operators with binary infix notation (flexary flag not supported yet) */
sealed abstract class InfixOperator(val symbol: String, val precedence: Int, val assoc: Associativity = NotAssociative)
  extends GeneralInfixOperator {
  def apply(l: Expression, r: Expression) = makeExpr(List(l, r))
  def unapply(e: Expression) = e match {
    case Application(BaseOperator(op,_), List(l,r)) if op == this => Some((l,r))
    case _ => None
  }
  def invertible = false
}

sealed abstract class Associativity
case object NotAssociative extends Associativity
case object Semigroup extends Associativity
case class Monoid(neut: Expression) extends Associativity
case object RightAssociative extends Associativity

/** operators with prefix notation */
sealed abstract class PrefixOperator(val symbol: String) extends Operator {
  def apply(e: Expression) = makeExpr(List(e))
  override def arity = Some(1)
  def invertible = true
}

// for type abbreviations
import BaseType._

/** generic code for operators that can act on numbers */
sealed trait NumberOperator extends Operator {
  /** pairs (A,F) such that if any input has type A, the operator has type F */
  val specialInputCases: List[(BaseType,FunType)] = Nil
  /** the output type is the union of all number types among the arguments unless that is adjusted here */
  def specialOutputCase(o: NumberType): BaseType = o
  /** finds all known number types among the arguments and assumes all unknown input types and the return type are their union */
  override def typeFor(ins: List[Type], out: Type, cbs: InferenceCallbacks): Option[FunType] = {
    specialInputCases.foreach {case (c, t) =>
      if (ins.contains(c)) return Some(t)
    }
    val ns = ins.collect {
      case n: NumberType => n
    }
    if (ns.isEmpty)
      None
    else {
      val nsU = ns.tail.fold(ns.head)(_ union _)
      val insS = ins.map {
        case n: NumberType => n
        case _ => nsU
      }
      val ft = SimpleFunType(insS, specialOutputCase(nsU))
      Some(ft)
    }
  }
}

/** arithmetic operators for number values */
sealed trait Arithmetic extends NumberOperator
/** comparison operators for number values and other types */
sealed trait Comparison extends NumberOperator {
  override val specialInputCases = List((B, B<--(B,B)), (S, B<--(S,S)))
  override def specialOutputCase(o: NumberType) = B
}

/** boolean connectives */
sealed trait Connective extends Operator {
  def apply(args: List[Expression]): Expression
  override val uniqueType = Some(B<--(B,B))
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

case object Not extends PrefixOperator("!") {
  override val uniqueType = Some(B <-- B)
}

/** implication a => b is the same as comparision a <= b; but we need a separate operator to get the right notation */
case object Implies extends InfixOperator("=>", -20, RightAssociative) with Connective {
  def apply(args: List[Expression]): Expression = apply(args.tail, args.last)
  def apply(ass: List[Expression], conc: Expression): Expression = ass match {
    case Nil => conc
    case _ => Implies(And(ass), conc)
  }
  override def isDynamic = true
}

case object Plus extends InfixOperator("+", 0, Semigroup) with Arithmetic {
  override val specialInputCases = List((S, S<--(S,S)))
  override def associative = true
  override def isolatableArguments = List(0,1)
  override def isolate(pos: Int, args: List[Expression], result: Expression) = {
    if (pos == 0) Some((args(0), Minus(result, args(1))))
    else if (pos == 1) Some((args(1), Minus(result, args(0))))
    else None
  }
}
case object Minus extends InfixOperator("-", 0) with Arithmetic {
  override def specialOutputCase(o: NumberType) = o.copy(negative = true)
  override def isolatableArguments = List(0, 1)
  override def isolate(pos: Int, args: List[Expression], result: Expression) = {
    if (pos == 0) Some((args(0), Plus(result, args(1))))
    else if (pos == 1) Some((args(1), UMinus(Minus(result, args(0)))))
    else None
  }
}
case object Times extends InfixOperator("*", 10, Monoid(NumberValue(1))) with Arithmetic {
  override def isolatableArguments = List(0, 1)
  override def isolate(pos: Int, args: List[Expression], result: Expression) = {
    if (pos == 0) Some((args(0), Divide(result, args(1))))// TODO args(1) != 0 check??
    else if (pos == 1) Some((args(1), Divide(result, args(0)))) // TODO args(0) != 0 check??
    else None
  }
}
case object Divide extends InfixOperator("/", 10) with Arithmetic  {
  override def specialOutputCase(o: NumberType) = o.copy(fractional = true)
  override def isolatableArguments = List(0, 1)
  override def isolate(pos: Int, args: List[Expression], result: Expression) = {
    if (pos == 0) Some((args(0), Times(result, args(1))))
    else if (pos == 1) Some((args(1), Divide(args(0), result)))
    else None
  }
}
case object Minimum extends InfixOperator("min", 10, Semigroup) with Arithmetic
case object Maximum extends InfixOperator("max", 10, Semigroup) with Arithmetic

case object Power extends InfixOperator("^", 20, RightAssociative) {
  override def typeFor(ins: List[Type], out: Type, cbs: InferenceCallbacks) = {
    val baseType = ins(0) match {
      case n: NumberType if !n.imaginary => n
      case _ => R
    }
    val expType = ins(1) match {
      case n: NumberType => n
      case _ => N
    }
    var ret = baseType
    if (baseType.negative) ret = ret.copy(imaginary = true)
    if (expType.negative) ret = ret.copy(fractional = true)
    if (expType.fractional) ret = ret.copy(approximate = true)
    Some(SimpleFunType(List(baseType, expType), ret))
  }
  override def isolatableArguments = List(0, 1)
  override def isolate(pos: Int, args: List[Expression], result: Expression) = {
    if (pos == 0) Some((args(0), Power(result, Divide(IntValue(1), args(1))))) // TODO args(1) != 0, result >= 0
    // TODO result und args(0) >= 0
    else if (pos == 1) Some((args(1), Divide(Application(OpenRef(Path(List("Math", "ln"))), List(result)), Application(OpenRef(Path(List("Math", "ln"))), List(args(0))))))
    else None
  }
}

case object UMinus extends PrefixOperator("-") with Arithmetic {
  override def specialOutputCase(o: NumberType) = o.copy(negative = true)
  override def isolatableArguments = List(0)
  override def isolate(pos: Int, args: List[Expression], result: Expression) = {
    if (pos == 0) Some((args(0), UMinus(result)))
    else None
  }
}

case object Less extends InfixOperator("<", -10) with Comparison
case object LessEq extends InfixOperator("<=", -10) with Comparison
case object Greater extends InfixOperator(">", -10) with Comparison
case object GreaterEq extends InfixOperator(">=", -10) with Comparison

/** generic code for operators on collections */
sealed trait CollectionOperator extends Operator {
  /** the inputs are assumed to be either elements or collections over elements; this gives the positions of the former */
  val elemIndices: List[Int]
  /** computes the type of the operators by taking the union of all element types */
  override def typeFor(ins: List[Type], out: Type, cbs: InferenceCallbacks) = {
    var elemTypes: List[Type] = Nil
    var kds: List[CollectionKind] = Nil
    val insW = ins.zipWithIndex
    insW.foreach {
      case (a, i) if a.known && elemIndices.contains(i) =>
        elemTypes ::= a
      case (c: CollectionType, _) =>
        kds ::= c.kind
        if (c.elem.known) elemTypes ::= c.elem
      case _ =>
    }
    out match {
      case c: CollectionType =>
        kds ::= c.kind
        if (c.elem.known) elemTypes ::= c.elem
      case _ =>
    }
    if (kds.isEmpty && elemTypes.isEmpty) {
      val a = cbs.unknown()
      val insS = insW.map {case (_,i) =>
        if (elemIndices.contains(i)) a else CollectionKind.List(a)
      }
      val outS = specialOutputCase(CollectionKind.List(a))
      val ft = SimpleFunType(insS, outS)
      Some(ft)
    } else {
      val kdsU = kds.fold(CollectionKind.List)(_ union _)
      val elemU = cbs.union(elemTypes)
      val coll = CollectionType(elemU,kdsU)
      val insS = insW.map {
        case (_,i) if elemIndices.contains(i) => elemU
        case _ => coll
      }
      val ft = SimpleFunType(insS, specialOutputCase(coll))
      Some(ft)
    }
  }
  /** the result type is the union of all collection types unless that is changed here */
  def specialOutputCase(c: CollectionType): Type = c
}

case object Concat extends InfixOperator(":::", -10, Monoid(CollectionKind.List(Nil))) with CollectionOperator {
  val elemIndices = Nil
}

case object In extends InfixOperator("in", -10) with CollectionOperator {
  val elemIndices = List(0)
  override def specialOutputCase(c: CollectionType) = BoolType
}

case object Cons extends InfixOperator("-:", -10, RightAssociative) with CollectionOperator {
  val elemIndices = List(0)
  override def invertible = true
}

case object Snoc extends InfixOperator(":-", -10) with CollectionOperator {
  val elemIndices = List(1)
  override def invertible = true
}

/** equality is a language primitive, not an operator,
 * but parsing is easiest if it is treated as a PseudoOperator and convert it into [Equality] later
 */
case object Equal extends PseudoInfixOperator("==") {
  override def precedence = -10
}
case object Inequal extends PseudoInfixOperator("!=") {
  override def precedence = -10
}

object Operator {
    val infixes: List[GeneralInfixOperator] = List(
      Plus, Minus, Times, Divide, Power,
      Minimum, Maximum,
      And, Or, Implies,
      Less, LessEq, Greater, GreaterEq,
      Concat, In, Cons, Snoc,
      Equal, Inequal
    ).sortBy(-_.length) // longer operators first for parsing
    val prefixes = List(UMinus, Not)

    def simplify(bo: BaseOperator, as: List[Expression]): Expression = {
      val o = bo.operator
      val numArgs = as.length
      def failNumArgs = throw IError(o.toString + " applied to " + numArgs + " arguments")
      o match {
        case pf: PrefixOperator =>
          if (numArgs != 1) failNumArgs
          ((pf, as.head)) match {
            case (UMinus, x: NumberValue) => x.negate
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
            case (Plus, x:NumberValue, y:NumberValue) => x plus y
            case (Minus, x:NumberValue, y:NumberValue) => x minus y
            case (Times, x:NumberValue, y:NumberValue) => x times y
            case (Divide, x:NumberValue, y:NumberValue) =>
              if (!y.tp.approximate && y.zero) throw ASTError("division by 0")
              else x divide y
            case (Power, RealValue(x), RealValue(y)) => RealValue(x power y)
            case (Minimum, x:NumberValue, y:NumberValue) => x min y
            case (Maximum, x:NumberValue, y:NumberValue) => x max y
            case (c: Comparison, x:NumberValue, y:NumberValue) =>
              val s = if (x eq y) 0 else if (x lessEq y) -1 else 1
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
            case (And, BoolValue(l), BoolValue(r)) => BoolValue(l && r)
            case (Implies, BoolValue(l), BoolValue(r)) => BoolValue(if (l) r else true)
            case (Or, BoolValue(l), BoolValue(r)) => BoolValue(l || r)
            case (Plus, StringValue(l), StringValue(r)) => StringValue(l + r)
            case (Concat, CollectionValue(l,lk), CollectionValue(r,rk)) =>
              CollectionValue(l ::: r, lk.union(rk))
            case (In, e, CollectionValue(es,_)) =>
              val b = es.contains(e)
              BoolValue(b)
            case (Cons, e, CollectionValue(es,k)) => CollectionValue(e :: es, k.copy(sizeOne=false))
            case (Snoc, CollectionValue(es,k), e) => CollectionValue(es ::: List(e), k.copy(sizeOne=false))
            case _ => throw IError("no case for operator evaluation: " + o.symbol)
          }
        case _: PseudoOperator => throw IError("unelaborated pseudo-operator")
      }
    }

    /** partial inverse, for pattern-matching */
    def invert(o: Operator, res: Expression): Option[List[Expression]] = {
      o match {
        case pf: PrefixOperator =>
          ((pf, res)) match {
            case (UMinus, x:NumberValue) =>
              Some(List(x.negate))
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
