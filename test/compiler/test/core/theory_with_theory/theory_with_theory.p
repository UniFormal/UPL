theory A {
  val x: int
}

theory B {
  val x: A
}

val x = B { x = A { x = 13 } }