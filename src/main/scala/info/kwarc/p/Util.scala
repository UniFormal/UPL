package info.kwarc.p

object Util {
  def noReps[A](l: List[A]): Boolean = {
    var left = l
    while (left.nonEmpty) {
      if (left.tail.contains(left.head)) return false
      left = left.tail
    }
    true
  }
  def distinct[A](l: List[A]) = {
    var left = l
    var res: List[A] = Nil
    while (left.nonEmpty) {
      val next = left.head
      if (!res.contains(next)) res ::= next
      left = left.tail
    }
    res.reverse
  }
  def disjoint[A](l: List[A], r: List[A]) = {
    l.forall(n => !r.contains(n))
  }
  def sub[A](l: List[A], r: List[A]) = {
    l.forall(n => r.contains(n))
  }
  def reverseMap[A,B](l: List[A])(f: A => B) = l.reverseIterator.map(f).toList
}