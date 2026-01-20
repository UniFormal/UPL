// A very simple and not quite trivial scroll, to test things
// Given two equal opaque points, the height of one is also the height of the other.
module minimal{
theory _point { type univ }
point: _point{ type univ = (int,int,int) }
//type point
height: point -> float = p -> p(3)

theory S1{
  P: point
  Q: point
}

theory S2{
  include S1
  E: |- P == Q
  H: (x:float, |- height(P) == x) = (42,???)
}

theory S3{
  include S2
  theory _Scroll{
    h1: (x:float, |- height(P) == x)
    h2 = h1(1) * 2
  }
  test1:_ = _Scroll{h1 = H}
}
}

module backup{
  // Code that wastes space in `minimal` rn, but I may want again later
type point
height: point -> float
theory _Scroll{
    p1: point
    p2: point
    h1: float
    h1_def: |- height(p1) == h1
    h2 = h1 * 2
    h2_def: |- height(p2) == h2
}

}