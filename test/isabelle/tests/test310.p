module Test310 {

    // top-level pattern-matching in function body can be compiled to Isabelle's pattern-matching function definition
    // with command "fun"

  // pattern-matching is written 'l match {pattern -> body, ...}'
  map2:_
  map2 = (l: [int]) -> (f: int -> int) -> {
    l match {
      [] -> []
      x -: xs -> f(x) -: map2(xs)(f)
    }
  }


}