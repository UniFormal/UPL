module Recursive-sum {


  sum: [int] -> int
  sum = (l: list[int]) -> {
    l match {
      [] -> 0
      h -: t -> h + sum(t)
    }
  }

}