module Recursive-factorial {

  // recursive function produces stack-overflow error.

  factorial2: int -> int
  factorial2 = x -> {
    if (x <= 0) return 1
    x * factorial2(x-1)
  }

}