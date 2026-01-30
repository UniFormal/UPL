package info.kwarc.p

/** joint parent class for all levels of contexts
 *  - global: all global declarations, i.e., the program's entire vocabulary.
 *   Names are unique due to qualification
 *  - regional: global + choice of theory relative to which expressions are formed.
 *   Duplicate names are merged
 *  - local: regional + locally bound variables.
 *   Duplicate names cause shadowing
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

  /** copies and appends some local declarations (c may be null) */
  def append(c: AbstractLocalContext[_,_<:VarDecl]): A = {
    if (c == null) copyLocal(local) else copyLocal(LocalContext(c.decls ::: decls))
  }
  def append(vd: VarDecl): A = append(LocalContext(vd))

  /** the prefix of this containing the first n local declarations (counting from outer-most) */
  def take(n: Int) = copyLocal(LocalContext(decls.drop(length - n)))

  /** the prefix of this without the last n local declarations (counting from outer-most) */
  def dropLast(n: Int) = copyLocal(LocalContext(decls.drop(n)))
  def split = (decls.last, LocalContext(decls.init))
  def getOutput = local.decls.collectFirst {
    case vd: EVarDecl if vd.name == "" && vd.output => vd.tp
  }
}

object -: {
  def unapply(l: LocalContext): Option[(VarDecl,LocalContext)] =
    if (!l.empty) Some(l.split) else None
  def unapply(l: ExprContext): Option[(EVarDecl,ExprContext)] =
    if (!l.empty) Some((l.decls.last,ExprContext(l.decls.init))) else None
}

/** parts of the implementation of LocalContext that are reusable */
sealed trait AbstractLocalContext[A,VD <: VarDecl] extends Context[LocalContext] {
  def variables: List[VD]
  // sharpen type
  override def decls: List[VD] = variables
  def copyLocal(lc: LocalContext) = lc
  override def toString = variables.reverse.mkString(", ")
  def label = "binding"
  def children = variables.reverse
  override def childrenInContext = variables.tails.toList.reverse.tail.map(l =>
    (None, Some(LocalContext(l.tail)), l.head)
  )
  /** the n-th declaration (counting from outer-most, starting at 0) */
  def apply(n: Int): VD = variables(length - 1 - n)
  def namesInOrder = domain.reverse
  def namesUnique = {
    val names = variables collect {case vd if !vd.anonymous => vd.name}
    Util.noReps(names)
  }
  def identity = Substitution(variables collect {
    case vd if !vd.anonymous => vd.toSub
  })
}
/** object-level context: relative to a vocabulary and a choice of theory in it
 *
 * Context-order means that the inner-most variables occurs first.
 * These are found first by lookup.
 * The constructors must not be applied to declarations in natural order - use make instead.
 */
case class LocalContext(variables: List[VarDecl]) extends AbstractLocalContext[LocalContext,VarDecl] {
  def local = this

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
  def substitute(os: List[Object]) = {
    if (variables.sizeIs != os.length)
      throw IError("unexpected number of substitutes")
    val defs = (variables zip os.reverse).map {
      case (vd: EVarDecl, o: Expression) =>
        EVarDecl.sub(vd.name,o)
      case (vd: TVarDecl, o: Type) =>
        TVarDecl.sub(vd.name,o)
      case _ => throw IError("unexpected substitute")
    }
    Substitution(defs)
  }
}

/** special case of LocalContext that contains only expressions
 * some, but not all, operations preserve the special case of typing
 */
case class ExprContext(variables: List[EVarDecl]) extends AbstractLocalContext[ExprContext,EVarDecl] {
  def toLocalContext = LocalContext(variables)
  def local = toLocalContext
  def appendE(vd: EVarDecl) = force(_.append(vd))
  def force(f: ExprContext => LocalContext) = ExprContext.force(f(this))

  def substitute(es: List[Expression]) = {
    if (variables.sizeIs != es.length)
      throw IError("unexpected number of values")
    val defs = (variables zip es.reverse).map {case (vd: EVarDecl, e) =>
      EVarDecl(vd.name, null, Some(e))
    }
    Substitution(defs)
  }
}
object ExprContext {
  val empty = ExprContext(Nil)
  def apply(vd: EVarDecl): ExprContext = ExprContext(List(vd))
  def make(vds: List[EVarDecl]) = ExprContext(vds.reverse)
  def force(lc: LocalContext) = ExprContext(lc.variables.asInstanceOf[List[EVarDecl]])
}
object LocalContext {
  val empty = LocalContext(Nil)
  def apply(d: VarDecl): LocalContext = LocalContext(List(d))
  def make(vds: List[VarDecl]) = LocalContext(vds.reverse)

  /** collects the declarations introduced by this expression */
  def collect(exp: Expression): List[EVarDecl] = exp match {
    case vd: EVarDecl =>
      val vdNoDef = if (vd.defined && vd.mutable) vd.copy(dfO = None) else vd
      vdNoDef :: collect(vd.dfO.toList)
    case Assign(t, v)        => collect(List(t, v))
    case Tuple(es)           => collect(es)
    case Projection(e, _)    => collect(e)
    case Application(f, as)  => collect(f :: as)
    case CollectionValue(es,_) => collect(es)
    case ListElem(l, i)      => collect(List(l, i))
    case OwnedExpr(o, _, _)  => collect(o)
    case _                   => Nil
  }
  def collect(exp: List[Expression]): List[EVarDecl] = exp.flatMap(collect)
  def collectContext(e: Expression) = LocalContext.make(collect(e))
}

/** parent of all variable declarations */
trait VarDecl extends Named {
  def tc = LocalContext.empty
  def dfO: Option[Object]
  def defined = dfO.isDefined
  def label = if (name != "") name else "_"
  def toRef = VarRef(name).copyFrom(this)
  def toSub: VarDecl
}

object VarDecl {
  def rename(a: VarDecl, b: VarDecl) = (a,b) match {
    case (_: EVarDecl, _:EVarDecl) => EVarDecl.sub(a.name, b.toRef)
    case (_: TVarDecl, _:TVarDecl) => TVarDecl.sub(a.name, b.toRef)
  }
}

/** substitution (for an omitted context) into a target context
 * (n_1/e_1 ... n_l/e_l) : (n_1:_, ..., n_l:_) -> target
 * represented as decls == VarDecl.sub(n_l,e_n), ...
 */
case class Substitution(decls: List[VarDecl]) extends HasChildren[VarDecl] {
  override def toString = decls.reverseIterator.map(vd => vd.name + "/" + vd.dfO.get).mkString(", ")
  def label = "substitution"
  def children = decls.map(_.dfO.get)

  /** e_1, ..., e_n */
  def exprs = Util.reverseMap(decls)(_.dfO.get)
  def map(f: VarDecl => VarDecl) = Substitution(
    Util.reverseMap(decls)(f).reverse
  )
  def take(n: Int) = Substitution(decls.drop(decls.length-n))

  /** this : G -> target   --->  this, n/e : G, n:_ -> target */
  def append(n: String, e: Expression) = copy(decls = EVarDecl.sub(n, e) :: decls)
  /** this : G -> target   --->  this, n/e : G, n:_ -> target */
  def append(n: String, t: Type) = copy(decls = TVarDecl.sub(n, t) :: decls)

  /** this : G -> target   --->  this, n/vd.name : G, n:_ -> target, vd */
  def appendRename(n: String, vd: VarDecl) = {
    val r = vd match {
        case _: EVarDecl => EVarDecl.sub(n, vd.toRef)
        case _: TVarDecl => TVarDecl.sub(n,vd.toRef)
      }
    Substitution(r::decls)
  }
  def appendRename(vd: VarDecl, n: String) = {
    val r = vd match {
      case _: EVarDecl => EVarDecl.sub(vd.name, VarRef(n))
      case _: TVarDecl => TVarDecl.sub(vd.name, VarRef(n))
    }
    Substitution(r::decls)
  }

  /** substitution is no-op */
  def isIdentity = decls.forall(d => d.anonymous || d.dfO.contains(VarRef(d.name)))

  /** if this is an injective renaming, the inverse */
  def inverse: Option[Substitution] = {
    var image: List[String] = Nil
    val subs = decls.collect {
      case vd @ EVarDecl(_, _, Some(VarRef(n)), _, _) if !vd.anonymous && !image.contains(n) =>
        image ::= n
        EVarDecl.sub(n, vd.toRef)
      case vd @ TVarDecl(_,Some(VarRef(n))) if !vd.anonymous && !image.contains(n) =>
        image ::= n
        TVarDecl.sub(n, vd.toRef)
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
  def append[A<:VarDecl](a: A, b: A) = BiContext((a, b) :: lr)
  def left = LocalContext(lr.map(_._1))
  def right = LocalContext(lr.map(_._2))
  def renameLeftToRight = Substitution(lr.map({case (a, b) => VarDecl.rename(a,b)}))
  def renameRightToLeft = Substitution(lr.map({case (a, b) => VarDecl.rename(b,a)}))
}

object BiContext {
  def apply(l: LocalContext, r: LocalContext): BiContext = BiContext(l.decls zip r.decls)
}

case class TVarDecl(name: String, dfO: Option[Type]) extends VarDecl with KindedDeclaration {
  override def toString = name
  def children = Nil
  def toSub = TVarDecl.sub(name, toRef)
}
object TVarDecl {
  def sub(n: String, t: Type) = TVarDecl(n,Some(t))
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
  val empty = apply(Theory.empty)
  def apply(thy: Theory, owner: Option[Expression] = None): RegionalContext =
    RegionalContext(thy, owner, LocalContext.empty)
  def apply(p: Path): RegionalContext = RegionalContext(PhysicalTheory(p))
}

/**
 * @param transparent subsequent frames may see this one (via .. for regional idents)
 * @param physical iff this represents a named module, whether it is closed; in that case, region.theory is just an include of that module
 */
case class RegionalContextFrame(region: RegionalContext, transparent: Boolean, physical: Option[Boolean]) {
  def isPhysicalOpen = physical contains false
  def isPhysicalClosed = physical contains true
}

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
 * Quoted regions block the visibility of all identifiers of the parent.
 * For owned regions, the visibility is still up for discussion, currently they are transparent.
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

  private def getCurrentTheoryValue = {
    if (inPhysicalTheory) parentDecl.df else {theory match {
      case r:Ref => lookupModule(r).df
      case thy => thy.toValue
    }}
  }

  /** lookup in the innermost region */
  def lookupRegional(name: String, noRecurse: Boolean = false): Option[NamedDeclaration] = {
    val tv = getCurrentTheoryValue
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
      // we need to skip the case where we look for super-theory t by following "include t" itself
      case ClosedRef(n) if !(name == n && noRecurse) => lookupRegional(n, true) match {
        case Some(m: Module) => m.lookupO(name).foreach {case d: NamedDeclaration => foundOne(d) case _ =>}
        case _ => // impossible for well-formed content, but could happen if we have previously recovered from unknown/wrong names
      }
      case _ =>
    }
    foundAbstract
  }

  /** looks up a symbol in the current region by notation and types */
  def lookupRegionalByNotation(pop: PseudoOperator, tpIn1: Option[Type], tpOut: Option[Type]): Option[ExprDecl] = {
    val tv = getCurrentTheoryValue
    var candidates: List[ExprDecl] = Nil
    tv.decls.foreach {
      case ed: ExprDecl =>
        if (ed.ntO.exists(nt => nt.fixity == pop.fixity && nt.symbol == pop.symbol)) {
          candidates ::= ed
          ed.tp match {
            case ft:FunType =>
              val matches = tpIn1.forall(_ == ft.inDecls.last.tp) && tpOut.forall(_ == ft.out)
              if (matches) return Some(ed)
            case _ =>
          }
        }
      case _ =>
    }
    // if only 1 declaration for the fixity exists, use it even if the types don't match
    if (candidates.sizeIs == 1)
      candidates.headOption
    else
      None
  }

  def lookupGlobal(p: Path) = {
    voc.lookupPath(p) match {
      case Some(d: SymbolDeclaration) if d.modifiers.closed => None
      case pL => pL
    }
  }

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
  // TODO this fails when traversing into a theory inside an anonymous theory; it's not clear what should happen in that case
  def enter(m: Module) = pushFrame(RegionalContext(currentParent / m.name), true, Some(m.closed))
  /** push an anonymous region */
  def enter(t: Theory): GlobalContext = pushFrame(RegionalContext(t.toValue), true, None)
  /** push an empty anonymous region */
  def enterEmpty() = pushFrame(RegionalContext.empty, true, None)
  /** push a referenced region */
  // We experimentally treat all regions as transparent (except for quoting); this used to make owned regions intransparent
  def push(t: Theory, owner: Option[Expression] = None): GlobalContext =
    pushFrame(RegionalContext(t, owner), true, None)
  def push(owners: FlatOwnedObject.Owners): GlobalContext = owners match {
    case Nil => this
    case hd::tl => push(hd._2,Some(hd._1)).push(tl)
  }
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
    if (this.regions.sizeIs != smaller.regions.length) return None
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
          if (regions.sizeIs > 1 && currentIsTransparent) {
            // current region is transparent and there is a previous one to try
            pop().resolvePath(p)
          } else None
      }
    }
  }
  /** resolves an ambiguous name */
  def resolveName(obj: Object): Option[(Object, Option[Named])] = {
    val (ref,args) = MaybeAppliedRef.unapply(obj).getOrElse{return Some((obj, None))}
    def make(r: Ref) = {
      val ra = MaybeAppliedRef(r,args)
      if (ra == obj) obj else ra.copyFrom(obj)
    }
    val n = ref match {
      case VarRef(n) => n
      case ClosedRef(n) => n
      case OpenRef(p) => return resolvePath(p) map {case (pR,d) => (make(OpenRef(pR)),Some(d))}
    }
    // try finding local variable n in context
    lookupLocal(n).foreach {vd =>
      return Some((make(VarRef(n)), Some(vd)))
    }
    // try finding n declared regionally in current or included module
    var gcO: Option[GlobalContext] = Some(this)
    while (gcO.exists(!_.regions.head.isPhysicalOpen)) {
      val gc = gcO.get
      gc.lookupRegional(n).foreach {d =>
        val level = regions.length - gc.regions.length + 1
        val ret = if (level > 1) {
          val owner = This(level)
          d match {
            case nd: NamedDeclaration =>
              val dO = OwnersSubstitutor.applyDecl(gc,nd,-level).asInstanceOf[NamedDeclaration]
              val objC = OwnedReference(owner,null,nd,args) // we keep the domain uninfered to avoid triggering checks later; but it will be inferred eventually anyway
              (objC.copyFrom(obj),Some(dO))
            case _ => throw IError("impossible case")
          }
        } else {
          (make(ClosedRef(n)), Some(d))
        }
        return Some(ret)
      }
      // look in transparent enclosing regions
      gcO = if (gc.regions.sizeIs > 1 && gc.currentIsTransparent) {
        Some(gc.pop())
      } else {
        None
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


