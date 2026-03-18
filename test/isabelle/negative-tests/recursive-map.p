module Recursive-map {


  // pattern-matching is written 'l match {pattern -> body, ...}'
  map2:_
  map2 = (l: [int]) -> (f: int -> int) -> {
    l match {
      [] -> []
      hd -: tl -> f(hd) -: map2(tl)(f)
    }
  }

}