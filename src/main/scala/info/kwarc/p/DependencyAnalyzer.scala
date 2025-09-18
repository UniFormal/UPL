package info.kwarc.p

class DependencyInterface {
  val provides = new PathSet(Path.empty)
  val uses = new PathSet(Path.empty)
  def clear() = {
    provides.clear()
    uses.clear()
  }
}

object DependencyAnalyzer {
  def update(entry: ProjectEntry) = {
    entry.depInter.clear()
    entry.parsed.decls.foreach {d => DependencyTraverser(d)(GlobalContext(Nil), entry.depInter)}
  }
}

object DependencyTraverser extends Traverser[DependencyInterface] {
  override def apply(d: Declaration)(implicit gc: GlobalContext, di: DependencyInterface): Declaration = {
    gc.inOpenModule foreach {p =>
      d.nameO.foreach {n =>
        di.provides add (p/n)
      }
    }
    applyDefault(d)
  }
  override def apply(p: Path)(implicit gc: GlobalContext, di: DependencyInterface): Path = {
    di.uses add p
    p
  }
}

/** a mutable set of paths, stored as a tree for efficient lookup */
class PathSet(root: Path) {
  private val children = new Util.ListMap[String,PathSet]
  private def getOrAddChild(s: String) = children(s).getOrElse {
    val ps = new PathSet(root/s)
    children(s) = ps
    ps
  }
  def add(p: Path): Unit = {
    if (!p.isRoot) {
      getOrAddChild(p.head).add(p.tail)
    }
  }
  def contains(p: Path): Boolean = {
    if (p.isRoot)
      true
    else
      children(p.head).exists(_.contains(p.tail))
  }
  def toList: List[Path] = if (children.isEmpty) List(root) else children.getEntries.flatMap(_._2.toList)
  override def toString = toList.mkString(", ")
  def clear(): Unit = {
    children.clear()
  }
}