module Basics011 {


  // Collection types are written using []:
  // - C[T] for the type
  // - C[x1,...,xn] for elements
  // - l[p] for positional access (if possible)
  // Here "C" can be set, list, bag, option. If omitted, it defaults to 'list'.
  ls: list[int] = [1,2,3,4]
  ls0 = ls[0] // Index bounds are not checked and may cause run-time errors.
  // -: and :- are cons and snoc.
  ls2 = 1 -: 2 -: [3] :- 4

}