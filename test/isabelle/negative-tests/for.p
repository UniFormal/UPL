module For {


  // for (x in L) {...} iterates over collections.
  foreach : ([int], int -> ()) -> () = (l,f) -> {for (i in l) f(i); ()}
  map = (l: [int]) -> f -> {
    var r: [int] = []
    for (x in l) {r = r :- f(x)}
    r
  }

  // Closures are taken when lambda-abstractions refer to mutable variables declared outside of the lambda.
  sum = l -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; ()
    }
    foreach(l,f)
    x
  }


}