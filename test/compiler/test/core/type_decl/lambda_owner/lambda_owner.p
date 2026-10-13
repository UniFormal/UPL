theory A {
  type tp
  val x: tp
}

lambda = () -> {
  10
}

val outer = A { type tp = int, x = lambda() }
