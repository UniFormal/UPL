package info.kwarc.p

/** parent of all classes in the AST */
trait SyntaxFragment {
  private[p] var loc: Location = null // set by parser to remember location in source

  def withLocation(l: Location): this.type = {
    loc = l
    this
  }
  def withLocationFromTo(f: SyntaxFragment,t:SyntaxFragment): this.type = {
    val l = if (f.loc == null) t.loc else if (t.loc == null) f.loc else f.loc extendTo t.loc
    withLocation(l)
  }

  def toStringShort: String = {
    val s = toString
    s.take(Math.min(20,s.length))
  }

  /** moves over mutable fields, may be called after performing traversals
   * if the resulting expression is "the same" as the original in some sense
   * if needed, it is usually to implement the traversal using also SyntaxFragment.matchC in the first place
   */
  def copyFrom(sf: SyntaxFragment): this.type = {
    loc = sf.loc
    this
  }

  /** short name for the kind of node, e.g., for display in an IDE */
  def label: String

  /** children of this AST node */
  def children: List[SyntaxFragment]

  /** children, paired with the additional context, must be overridden if context changes for any child */
  def childrenInContext: List[SyntaxFragment.Child] = cf(children: _*)

  /** convenience to build children list if no context is changed */
  protected def cf(fs: SyntaxFragment*): List[SyntaxFragment.Child] =
    fs.toList.map(c => (None, None, c))

  /** the origin of this element (if no location, depth-first descendant with location) */
  def origin: SourceOrigin = if (loc != null) loc.origin else {
    children.foreach { c =>
      val o = c.origin
      if (o != null) return o
    }
    null
  }

  /** path to a source position */
  def pathTo(at: Location): Option[List[SyntaxFragment.PathSegment]] = {
    if (loc == null || (loc != null && loc.contains(at))) {
      childrenInContext.foreach {case (r, l, s) =>
        val pO = s.pathTo(at)
        pO.foreach {p => return Some((this, r, l) :: p)}
      }
      if (loc == null) None else Some(List((this, None, None)))
    } else
      None
  }

  /** same but for an offset */
  def pathTo(at: Int): Option[List[SyntaxFragment.PathSegment]] = pathTo(Location(origin, at, at))

  /** object at a source position and its context
   * @param gc the context of this element
   */
  def descendantAt(gc: GlobalContext, at: Location): Option[(GlobalContext, SyntaxFragment)] = {
    val p = pathTo(at).getOrElse {return None}
    p.lastOption.map {d =>
      var gcI = gc
      p.foreach {
        case (m:Module,_,_) =>
          gcI = gcI.enter(m)
        case (_,tO,lO) =>
          tO.foreach {t => gcI = gcI.push(t)}
          lO.foreach {l => gcI = gcI.append(l)}
      }
      (gcI, d._1)
    }
  }

  /** same but for an offset */
  def descendantAt(gc: GlobalContext,at: Int): Option[(GlobalContext, SyntaxFragment)] =
    descendantAt(gc, Location(origin, at, at))
}

object SyntaxFragment {
  /** applies a function, usually by case-matching, and copies mutable data over (see copyFrom) */
  def matchC[A <: SyntaxFragment](a: A)(f: A => A): A = {
    val fa = f(a)
    if (fa != null) fa.copyFrom(a) else fa
  }

  /** child of a SyntaxFragment, with the context introduced by the parent */
  type Child = (Option[Theory], Option[LocalContext], SyntaxFragment)

  /** a SyntaxFragment with the context introduced for a particular child */
  type PathSegment = (SyntaxFragment, Option[Theory], Option[LocalContext])
}

trait MaybeNamed extends SyntaxFragment {
  def nameO: Option[String]
}

trait Named extends MaybeNamed {
  def name: String
  def nameO: Some[String] = Some(name)
  def anonymous = name == ""
}

trait HasChildren[A <: MaybeNamed] extends SyntaxFragment {
  def decls: List[A]
  def domain = decls collect {case d: Named => d.name}
  def length = decls.length
  def empty = decls.isEmpty
  def lookupO(name: String) = decls.find(_.nameO.contains(name))
  def lookup(name: String) = lookupO(name).get
  def declares(name: String) = lookupO(name).isDefined
}

/** identifiers */
case class Path(names: List[String]) extends SyntaxFragment {
  override def toString = names.mkString(".")
  def head = names.head
  def tail = Path(names.tail)
  def /(n: String) = Path(names ::: List(n))
  def /(p: Path) = Path(names ::: p.names)
  def up = Path(names.init)
  def name = names.last
  def isRoot = names.isEmpty
  def isToplevel = names.length == 1
  def label = toString
  def children = Nil
}

object Path {
  val empty = Path(Nil)
  def apply(ns: String*): Path = Path(ns.toList)
}

/** reference to a source location
 * @param origin source document/file
 * @param from begin offset (inclusive)
 * @param to end offset (exclusive)
 * all line ending characters are counted
 */
case class Location(origin: SourceOrigin, from: Int, to: Int) {
  override def toString = s"$origin#$from:$to"
  def contains(that: Location): Boolean = this.origin == that.origin && this.from <= that.from && that.to <= this.to
  def contains(that: Int): Boolean = contains(Location.single(origin, that))
  def extendTo(l: Location) = copy(to=l.to)
}

object Location {
  def single(o: SourceOrigin, p: Int) = Location(o,p,p+1)
}
