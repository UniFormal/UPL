module Mutual-rec {

  // produces stackoverflow error

  odd: int -> _  // inferrable types can be omitted even with recursive functions
  even = x -> (x == 0) | if (x>0) odd(x-1) else odd(-x-1)
  odd = x -> if (x == 0) false else even(x-1)

}