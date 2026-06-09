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
// Compiler cant currently support this, because the memory layout of the
// two types is different.
inst: B = C { }
