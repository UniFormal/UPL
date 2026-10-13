theory A {
  a: int = 2
  b: int
}
theory B {
  include A
}

b = B { b = 3 }
