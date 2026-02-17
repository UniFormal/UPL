module Basics001 {
  // Atomic declaration in a module/theory can be for types and terms (values).
  type a = int
  val c1: a = 0
  // The keyword "val" may be omitted. Types are inferred if omitted.
  c2 = 0
}