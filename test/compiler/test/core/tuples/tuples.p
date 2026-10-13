theory A {
  val x: int
  val y: (int, int)
}

val comp = (32, true, 15, 5, false, "a")
val comp2 = (5, false, 10, 2, true, "abc")
val comp3 = ("hello", 10, false)

val inst = A { x = 5, y = (2, 3) }