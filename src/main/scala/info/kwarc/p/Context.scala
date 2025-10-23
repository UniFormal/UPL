package info.kwarc.p

import java.time.chrono.ChronoLocalDate

/** joint parent class for all levels of contexts
 *  - global: all global declarations, i.e., the program's entire vocabulary
 *   names are unique due to qualification
 *  - regional: global + choice of theory relative to which expressions are formed
 *   duplicate names are merged
 *  - local: regional + locally bound variables
 *   duplicate names cause shadowing
 *
 * Implementation-wise, it is more convenient to group the contexts in such a way that each subsumes the smaller ones.
 * Thus, in particular, every context has a local context.
 */
abstract class Context[A] extends SyntaxFragment with HasChildren[VarDecl] {

  /** the local context */
  def local: LocalContext
  def decls = local.variables

  /** helps create copies with a different local context */
  def copyLocal(lc: LocalContext): A

  /** copies and appends some local declarations */
  def append(c: LocalContext) = copyLocal(LocalContext(c.variables ::: decls))
  def append(vd: VarDecl): A = append(LocalContext(vd))

  /** the prefix of this containing the first n local declarations (counting from outer-most) */
  def take(n: Int) = copyLocal(LocalContext(decls.drop(length - n)))

  /** the prefix of this without the last n local declarations (counting from outer-most) */
  def dropLast(n: Int) = copyLocal(LocalContext(decls.drop(n)))
  def getOutput = local.decls.find(vd => vd.name == "" && vd.output).map(_.tp)
}

/** object-level context: relative to a vocabulary and a choice of theory in it
 *
 * Context-order means that the inner-most variables occurs first.
 * These are found first by lookup.
 * The constructors must not be applied to declarations in natural order - use make instead.
 */
case class LocalContext(variables: List[VarDecl]) extends Context[LocalContext] {
  override def toString = variables.reverse.mkString(", ")
  def label = "binding"
  def children = variables.reverse
  override def childrenInContext = variables.tails.toList.reverse.tail.map(l =>
    (None, Some(LocalContext(l.tail)), l.head)
  )
  def local = this
  def copyLocal(lc: LocalContext) = lc

  /** the n-th declaration (counting from outer-most, starting at 0) */
  def apply(n: Int) = variables(length - 1 - n)

  /** checks if this == smaller.append(result) */
  def unappend(smaller: LocalContext): Option[LocalContext] = {
    val thisLen = this.length
    val smallerLen = smaller.length
    if (thisLen < smallerLen) return None
    val (diff, rest) = variables.splitAt(thisLen - smallerLen)
    if (rest != smaller.variables)
      return None // should be reference equality in practice and return immediately
    Some(LocalContext(diff))
  }

  /** applies f to all declarations, outer-most first */
  def map(f: VarDecl => VarDecl) = {
    LocalContext.make(this mapDecls f)
  }
  /** applies f to all declarations, outer-most first */
  def mapDecls[B](f: VarDecl => B) = {
    Util.reverseMap(variables)(f)
  }
  def namesInOrder = domain.reverse
  def namesUnique = {
    val names = variables collect {case vd if !vd.anonymous => vd.name}
    Util.noReps(names)
  }

  def substitute(es: List[Expression]) = {
    if (variables.length != es.length)
      throw IError("unexpected number of values")
    val defs = (variables zip es.reverse).map {case (vd, e) =>
      VarDecl(vd.name, null, Some(e))
    }
    Substitution(defs)
  }
  def identity = Substitution(variables collect {
    case vd if !vd.anonymous => vd.toSub
  })
}
object LocalContext {
  val empty = LocalContext(Nil)
  def apply(d: VarDecl): LocalContext = LocalContext(List(d))
  def make(vds: List[VarDecl]) = LocalContext(vds.reverse)

  /** collects the declarations introduced by this expression */
  def collect(exp: Expression): List[VarDecl] = exp match {
    case vd: VarDecl =>
      val vdNoDef = if (vd.defined && vd.mutable) vd.copy(dfO = None) else vd
      List(vdNoDef)
    case Assign(t, v)        => collect(List(t, v))
    case Tuple(es)           => collect(es)
    case Projection(e, _)    => collect(e)
    case Application(f, as)  => collect(f :: as)
    case CollectionValue(es,_) => collect(es)
    case ListElem(l, i)      => collect(List(l, i))
    case OwnedExpr(o, _, _)  => collect(o)
    case _                   => Nil
  }
  def collectContext(e: Expression) = LocalContext(collect(e))
  def collect(exp: List[Expression]): List[VarDecl] = exp.flatMap(collect)
}

/** substitution (for an omitted context) into a target context
 * (n_1/e_1 ... n_l/e_l) : (n_1:_, ..., n_l:_) -> target
 * represented as decls == VarDecl.sub(n_l,e_n), ...
 */
case class Substitution(decls: List[VarDecl]) extends HasChildren[VarDecl] {
  override def toString =
    decls.reverseIterator.map(vd => vd.name + "/" + vd.dfO.get).mkString(", ")
  def label = "substitution"
  def children = decls.map(_.dfO.get)

  /** e_1, ..., e_n */
  def exprs = Util.reverseMap(decls)(_.dfO.get)
  def map(f: VarDecl => VarDecl) = Substitution(
    Util.reverseMap(decls)(f).reverse
  )
  def take(n: Int) = Substitution(decls.drop(decls.length-n))

  /** this : G -> target   --->  this, n/e : G, n:_ -> target */
  def append(n: String, e: Expression) =
    copy(decls = VarDecl.sub(n, e) :: decls)

  /** this : G -> target   --->  this, n/vd.name : G, n:_ -> target, vd */
  def appendRename(n: String, vd: VarDecl) = Substitution(
    VarDecl.sub(n, vd.toRef) :: decls
  )

  /** substitution is no-op */
  def isIdentity =
    decls.forall(d => d.anonymous || d.dfO.contains(VarRef(d.name)))

  /** if this is an injective renaming, the inverse */
  def inverse: Option[Substitution] = {
    var image: List[String] = Nil
    val subs = decls.collect {
      case vd @ VarDecl(_, _, Some(VarRef(n)), _, _)
        if !vd.anonymous && !image.contains(n) =>
        image ::= n
        VarDecl.sub(n, vd.toRef)
      case _ => return None
    }
    Some(Substitution(subs))
  }
}
object Substitution {
  def empty = Substitution(Nil)
}

/** a pair of alpha-renamable contexts, with the substitutions between them
 * This is helpful when matching dependent types up to alpha-renaming in a way that delays substitutions.
 */
case class BiContext(lr: List[(VarDecl, VarDecl)]) {
  def append(a: VarDecl, b: VarDecl) = BiContext((a, b) :: lr)
  def left = LocalContext(lr.map(_._1))
  def right = LocalContext(lr.map(_._2))
  def renameLeftToRight = Substitution(lr.map({case (a, b) => VarDecl.sub(a.name, b.toRef)}))
  def renameRightToLeft = Substitution(lr.map({case (a, b) => VarDecl.sub(b.name, a.toRef)}))
}

object BiContext {
  def apply(l: LocalContext, r: LocalContext): BiContext = BiContext(l.decls zip r.decls)
}

/** declaration-level context: relative to a vocabulary, holds a regional+local context
 * @param theory the regional context: a theory
 * @param owner the instance whose domain makes the regional context
 *   if this is defined, [[theory]] may be null, in which case it has to be infered
 * @param local the local context
 */
case class RegionalContext(theory: Theory, owner: Option[Expression], local: LocalContext) extends Context[RegionalContext] {
  override def toString = owner.getOrElse(theory).toString + s"($local)"
  def label = "region"
  def children = theory :: local.children
  override def childrenInContext =
    (None, None, theory) :: local.childrenInContext.map {case (_, l, c) => (Some(theory), l, c)}
  def copyLocal(c: LocalContext) = copy(local = c)
  def add(d: Declaration) = copy(theory = theory.toValue.add(d))
}
object RegionalContext {
  val empty = RegionalContext(Theory.empty, None, LocalContext.empty)
  def apply(thy: Theory, owner: Option[Expression] = None): RegionalContext = RegionalContext(thy, owner, LocalContext.empty)
  def apply(p: Path): RegionalContext = RegionalContext(PhysicalTheory(p))
}

/**
 * @param transparent subsequent frames may see this one (via .. for regional idents)
 * @param physical iff this represents a named module, whether it is closed; in that case, region.theory is just an include of that module
 */
case class RegionalContextFrame(region: RegionalContext, transparent: Boolean, physical: Option[Boolean])

/** program-level context: provides the vocabulary and the stack of regional+local contexts
 *
 * @param voc the vocabulary
 * @param regions a stack of regional contexts
 *
 * Traverser algorithms must move between regional contexts such as
 * Therefore, they are maintained as a stack
 * - physical: named regions encountered when defining a module/theory
 * - anonymous: theories used to create new instances and class types
 * - referenced: owned and quoted objects (owner is stored in regional context)
 * The top element is the current region and provides the semantics of regional identifiers.
 * Physical and anonymous regions are transparent: They allow accessing their parent through "..".
 * Referenced regions block the visibility of all identifiers of the parent.
 */
case class GlobalContext private (voc: Module, regions: List[RegionalContextFrame]) extends Context[GlobalContext] {
  def label = "global"
  def children = regions.map(_.region)
  def currentRegion = regions.head.region
  def currentIsTransparent = regions.head.transparent
  def theory = currentRegion.theory
  def local = currentRegion.local
  def visibleLocals = {
    val i = regions.indexWhere(!_.transparent)
    val vis = if (i == -1) regions else regions.take(i+1) // take all transparent regions and the next one
    LocalContext(vis.flatMap(_.region.local.decls))
  }
  def freshName = {
    var i = 0
    while (local.decls.exists(vd => vd.name.startsWith("_" + i))) i += 1
    "_" + i
  }

  // lookups

  def lookupLocal(name: String): Option[VarDecl] = {
    var regs = regions
    while (regs.nonEmpty) {
      val r = regs.head
      val vdO = r.region.local.lookupO(name)
      if (vdO.isDefined) return vdO
      if (r.transparent) regs = regs.tail
      else regs = Nil
    }
    None
  }

  /** lookup in the innermost region */
  def lookupRegional(name: String): Option[NamedDeclaration] = {
    val tv = if (inPhysicalTheory) parentDecl.df else {theory match {
      case r:Ref => lookupModule(r).df
      case thy => thy.toValue
    }}
    // look in the current module for a primitive or previously merged declaration
    tv.lookupO(name) match {
      case Some(nd: NamedDeclaration) if nd.modifiers.closed => return Some(nd)
      case _ =>
    }
    // look in included modules (only relevant for theories, that are not fully flat)
    if (tv.flatness == Theory.FullyFlat) return None
    // return the first found defined declaration; if none, return any abstract one
    var foundAbstract: Option[NamedDeclaration] = None
    val foundOne = (d: NamedDeclaration) => {
      if (d.modifiers.closed && !d.subsumed) {
        if (d.defined) return Some(d)
        else foundAbstract = Some(d)
      }
    }
    tv.supers.foreach {
      case OpenRef(p) => voc.lookupPath(p / name).foreach(foundOne)
      case ClosedRef(n) => lookupRegional(n) match {
        case Some(m: Module) => m.lookupO(name).foreach {case d: NamedDeclaration => foundOne(d) case _ =>}
        case Some(_) => throw IError("not a module")
        case None => throw IError("unknown name")
      }
      case _ =>
    }
    foundAbstract
  }

  def lookupGlobal(p: Path) = voc.lookupPath(p)

  def lookupRef(r: Ref) = r match {
    case OpenRef(p) => lookupGlobal(p)
    case ClosedRef(n) => lookupRegional(n)
    case VarRef(n) => lookupLocal(n)
  }

  /** lookup a module that is known to exist */
  def lookupModule(r: Ref) = lookupRef(r) match {
    case Some(m: Module) => m
    case Some(_) => throw ASTError("not a module")
    case None => throw ASTError("not a name")
  }

  // updates to stack of regional contexts

  /** push a physical region */
  def enter(m: Module) = pushFrame(RegionalContext(currentParent / m.name), true, Some(m.closed))
  /** push an anonymous region */
  def enter(t: Theory): GlobalContext = pushFrame(RegionalContext(t.toValue), true, None)
  /** push an empty anonymous region */
  def enterEmpty() = pushFrame(RegionalContext.empty, true, None)
  /** push a referenced region (transparent if no owner) */
  def push(t: Theory, owner: Option[Expression] = None): GlobalContext =
    pushFrame(RegionalContext(t, owner), owner.isEmpty, None)
  /** push an instransparent referenced region */
  def pushQuoted(t: Theory): GlobalContext =
    pushFrame(RegionalContext(t, None), false, None)
  private def pushFrame(r: RegionalContext, trans: Boolean, phys: Option[Boolean]) = {
    val f = RegionalContextFrame(r, trans, phys)
    copy(regions = f :: regions)
  }
  /** removes last region */
  def pop() = {
    // The code below yields the rule Q, x:U |- `e`: A  if  T, x:Q{U} |- e: Q{A}
    // It's tempting but too strong because it would make pattern-matching available on x:N{U} even though x:U extends the open world of Q.
    /*val thy = currentRegion.theory
    val quotedLocals = currentRegion.local.map {vd =>
      vd.copy(tp = ExprsOver(thy, vd.tp), dfO = vd.dfO map {d => ExprOver(thy, d)})
    }
    val popped = copy(regions = regions.tail)
    popped.append(quotedLocals)*/
    copy(regions = regions.tail)
  }

  def copyLocal(lc: LocalContext) = {
    val regC = currentRegion.copyLocal(lc)
    copy(regions = regions.head.copy(region = regC) :: regions.tail)
  }

  // changes to current region

  /** adds a declaration to the current physical theory (if any) or the current region */
  def add(d: Declaration) = {
    if (inPhysicalTheory) {
      copy(voc = voc.addIn(currentParent, d))
    } else {
      val frame :: tail = regions
      val frameA = frame.copy(region = frame.region.add(d))
      copy(regions = frameA :: tail)
    }
  }

  /** checks if this == smaller.append(result) */
  def unappend(smaller: GlobalContext): Option[LocalContext] = {
    // voc may be longer than shorter.voc, but that is not checked here
    if (this.regions.length != smaller.regions.length) return None
    if (this.regions.tail != smaller.regions.tail)
      return None // should be reference equal in practice and succeed immediately
    this.currentRegion.local unappend smaller.currentRegion.local
  }

  /** true if the local environment is given by the current parent(s) (as opposed to other ones that we have pushed) */
  private def inPhysicalTheory = regions.forall(_.physical.isDefined)

  /** the path to the current theory if in physical theory */
  private def currentParent: Path = {
    if (!inPhysicalTheory)
      throw IError("not in physical theory")
    else currentRegion.theory match {
      case PhysicalTheory(p, _) => p
      case _ => throw IError("not a physical theory")
    }
  }
  /** the current theory if in physical theory */
  def parentDecl = voc.lookupModule(currentParent).getOrElse {
    throw ASTError("unknown parent: " + currentParent)
  }

  /** returns the current open module if we are in one */
  def inOpenModule = if (regions.forall(_.physical.contains(false))) Some(currentParent) else None

  /** declarations of the current parent/region */
  def parentDecls = {
    if (inPhysicalTheory) parentDecl.decls
    else currentRegion.theory.decls
  }

  // heuristic lookup of names from surface syntax, also return internal name

  /** dereferences an ambiguous relative path: looks up in transparent physical parent regions and returns the first that exists */
  def resolvePath(p: Path): Option[(Path, NamedDeclaration)] = {
    if (!inPhysicalTheory) {
      currentRegion.theory.toValue.lookupPath(p) match {
        case Some(d) => Some((p, d))
        case None    => pop().resolvePath(p)
      }
    } else {
      val pp = currentParent / p
      voc.lookupPath(pp) match {
        case Some(d) => Some((pp, d))
        case None =>
          if (regions.length > 1 && currentIsTransparent) {
            // current region is transparent and there is a previous one to try
            pop().resolvePath(p)
          } else None
      }
    }
  }
  /** resolves an ambiguous name */
  def resolveName(obj: Object): Option[(Object, Option[NamedDeclaration])] = {
    def make(e: Object) = if (e == obj) obj else e.copyFrom(obj)
    val n = obj match {
      case VarRef(n) => n
      case ClosedRef(n) => n
      case OpenRef(p) => return resolvePath(p) map {case (pR,d) => (OpenRef(pR),Some(d))}
      case _ => return Some((obj, None))
    }
    // try finding local variable n in context
    lookupLocal(n).foreach {vd =>
      return Some((make(VarRef(n)), Some(vd)))
    }
    // try finding n declared regionally in current or included module
    var gcO: Option[GlobalContext] = Some(this)
    while (gcO.isDefined) {
      val gc = gcO.get
      gc.lookupRegional(n).foreach {d =>
        val level = regions.length - gc.regions.length + 1
        val ret = if (level > 1) {
          val owner = This(level)
          d match {
            case nd: NamedDeclaration =>
              val dO = OwnersSubstitutor.applyDecl(gc,nd,-level).asInstanceOf[NamedDeclaration]
              val objC = OwnedReference(owner,null,nd) // we keep the domain uninfered to avoid triggering checks later; but it will be inferred eventually anyway
              (objC,Some(dO))
            case _ => throw IError("impossible case")
          }
        } else {
          (make(ClosedRef(n)), Some(d))
        }
        return Some(ret)
      }
      // look in transparent enclosing regions
      if (gc.regions.length > 1 && gc.currentIsTransparent) {
        gcO = Some(gc.pop())
      } else {
        gcO = None
      }
    }
    // try finding n declared globally in current module or parent modules
    resolvePath(Path(n)) foreach {case (p,d) =>
      return Some((make(OpenRef(p)), Some(d)))
    }
    // give up
    None
  }
}

object GlobalContext {
  def apply(n: String): GlobalContext = GlobalContext(Module(n, false, Nil))
  def apply(decls: Iterable[Declaration]): GlobalContext = GlobalContext(Module.anonymous(decls.toList))
  def apply(v: TheoryValue): GlobalContext = GlobalContext(Module.anonymous(v.decls))
  def apply(m: Module): GlobalContext = GlobalContext(m, List(RegionalContextFrame(RegionalContext(Path.empty), true, Some(m.closed))))
}


