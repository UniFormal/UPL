module Interval-types {

  // interval types

      // interval types
      // Isabelle does not have native interval types, thus throw IError
      // Maybe look at the HOL-Library.Interval or the Interval_Analysis entry in the Archive of Formal Proofs (AFP)

      n: int[0;10] = 0

    type a = int
    val c1: a = 0
    // The keyword "val" may be omitted. Types are inferred if omitted.
    c2 = 0
    // Interval types can be formed as subtypes of int.
    // This makes type-checking undecidable, but the checker tries its best and fails if it cannot verify the type.
    c3: int[0;2] = c1
    c4: (x:int, y:int[0;x]) = (1,0)
    // The intervals can be unbounded on either side.
    type nat = int[0;]



}