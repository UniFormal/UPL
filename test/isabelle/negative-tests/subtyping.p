module Subtyping {


  // outputs option value (Some 3) for list value [5]
  ls2 = 1 -: 2 -: [3] :- 4

  // outputs option value (None) for list value []
  map2:_
  map2 = (l: [int]) -> (f: int -> int) -> {
    l match {
      [] -> []
      x -: xs -> f(x) -: map2(xs)(f)
    }
  }

}