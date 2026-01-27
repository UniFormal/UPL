package info.kwarc.p

/** fragment of a larger source but processed independently, e.g., a notebook cell */
case class SourceOrigin(container: String, fragment: String = null) {
  def isAnonymous = container == null
  def isStandalone = fragment == null
  override def toString = (if (container != null) container else "_") + (if (fragment != null) "?" + fragment else "")
}

object SourceOrigin {
  private var counter = -1
  def shell(id: Int) = SourceOrigin("shell", id.toString)
  def anonymous = {
    counter += 1
    SourceOrigin(null, counter.toString)
  }
}

