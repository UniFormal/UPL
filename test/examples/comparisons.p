// Comparisons of equal numbers and singleton intervals.
// `x eq y` used to be reference equality, so equal numbers compared as "less than":
// 2>=2 was false, 2<2 was true, and int[2;2] was the empty type.
module Comparisons {
  n2: int = 2

  boundary = () -> {
    ASSERT(2>=2, true)
    ASSERT(2<=2, true)
    ASSERT(2<2, false)
    ASSERT(2>2, false)
    ASSERT(n2>=2, true)
    ASSERT(n2<2, false)
    ASSERT(1>=2, false)
    ASSERT(3>=2, true)
    ASSERT(2<3, true)
    ASSERT(3<2, false)
    ASSERT((1/2)>=(1/2), true)
    ASSERT((1/2)<(1/2), false)
    ASSERT(2.0>=2.0, true)
    ASSERT(2.0<2.0, false)
    ASSERT(2>=2.0, true)
    ()
  }

  // a singleton interval is inhabited, a reversed one is empty
  type One = int[2;2]
  one: One = 2

  test = {
    boundary()
    ASSERT(one, 2)
    true
  }
}
