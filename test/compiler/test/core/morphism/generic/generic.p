theory A {
  a: int
  b: int
}
theory B {
  b: int
  a: int
}
theory C {
  include A
  include B
  a = 2
  b = 3
}
inst: B = C { }
