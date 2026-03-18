module Assign {


  // Variable declarations and assignments may use a pattern on the LHS
  ac = {
    val abc = ["a", "b", "c"];
    // split 'abc' into "a" -: ["b","c"] and assign a = "a"
    (val a) -: _ = abc;
    // c = "c" accordingly
    _ :- (val c) = abc;
    (a,c)
  }

}