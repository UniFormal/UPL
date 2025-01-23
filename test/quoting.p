module Q {
  class N {
    type n
    z: n
    s: n -> n
  }

  zero = N{z}
  one = N{s(z)}
  two = N{s(`one`)}
  succ = (x:N.n) -> N{s(`x`)}
  pred = x -> x match {
    N.z -> N.z
    N{s(`p`)} -> p
  }

  test = succ(zero) == one & pred(two) == one
}