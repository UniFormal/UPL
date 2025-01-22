module Q {
  class N {
    type n
    z: n
    s: n -> n
  }

  c = N{z}
  sf = (x:N.n) -> N{s(`x`)}
  pf = x -> x match {
    N.z -> N.z
    N{s(`p`)} -> p
  }
}