module While-factorial {

  factorial = (x:int) -> {
    // return statements return from the current named function (even if the return type has not been infered yet).
    if (x<0) return 1
    // var/val introduce immutable/mutable variables that are visible for the remainder of the block.
    // Types can be inferred, initialization is mandatory.
    var result = 1
    var i = 1
    // if and while can be used as usual.
    while (i<=x) {
      result = result*i
      i = i+1
    }
    // no "return" needed for the last expression
    result
  }


}