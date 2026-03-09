module Basics010 {

  // Boolean operators:
  conj(x,y:: bool): bool = x & y
  impl(x,y:: bool): bool = x => y
  disj(x,y:: bool): bool = x | y
  neg(x: bool): bool = !x

  // All binary operators short-circuit.
  // Theorem provers may assume the truth (resp. falsity) of x when processing x&y or x=>y (resp. x|y).
  no_exception = false & (1/0 == 1)



}