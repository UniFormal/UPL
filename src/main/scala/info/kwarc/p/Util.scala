package info.kwarc.p

object Util {
  def noReps[A](l: List[A]) = l.distinct.length == l.length
  def disjoint[A](l: List[A], r: List[A]) = {
    l.forall(n => !r.contains(n))
  }
  def sub[A](l: List[A], r: List[A]) = {
    l.forall(n => r.contains(n))
  }
  def reverseMap[A,B](l: List[A])(f: A => B) = l.reverseIterator.map(f).toList
}