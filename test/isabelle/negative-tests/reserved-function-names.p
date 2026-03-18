module Reserved-function-names {

  // The following compilation fails Isabelle type-checking because hd, tl are reserved words for built-in functions.

  map2:_
  map2 = (l: [int]) -> (f: int -> int) -> {
    l match {
      [] -> []
      hd -: tl -> f(hd) -: map2(tl)(f)
    }
  }


}