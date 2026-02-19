module Test015x {

  // recursive functions

  //factorial2: int -> int
  factorial2: int -> int = x -> {
    if (x <= 0) return 1
    x * factorial2(x-1)
  }


}