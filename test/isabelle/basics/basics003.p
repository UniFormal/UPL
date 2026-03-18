module Basics003 {

  f1 : int -> int = (x:int) -> x+1
  f2 = (x:int) -> x+1
  f3 : int -> int = x -> x+1
  f4 : int -> _ = x -> x+1
  f5_multiarg: (int,int) -> int = (x,y) -> x+y
  f5_multiarg_applied = f5_multiarg(0,1)
  f5_curried:   int -> int -> int = x -> y -> x+y
  f5_curried_applied = f5_curried(0)(1)
  f5_multiarg_variant(x: int,y:int): int = x+y

}