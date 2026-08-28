theory A {
  a: int
  b: int
}
theory B {
  b: int
  c: int
}
theory C {
  a: int
  c: int
}
theory D {
  include A
  include B
  include C
}

d: A = D { a = 1, b = 2, c = 3 }
d2: B = D { a = 4, b = 5, c = 6 }
