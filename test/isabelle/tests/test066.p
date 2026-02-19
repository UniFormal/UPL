module Test066 {

  // polymorphic function composition
  comp@(A,B,C)(f: A -> B, g: B -> C) = x -> g(f(x))


}