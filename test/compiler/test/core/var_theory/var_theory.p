theory A {
  val x: int
}

test = () -> {
  var a = A { x = 10 }

  a.x
}