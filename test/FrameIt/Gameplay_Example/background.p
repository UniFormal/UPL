// The Background declares all relevant types and functions
// No modules, because UPL struggles with modules rn
type point
type triangle = (point,point,point)
dist: point -> point -> float
similar: triangle -> triangle -> bool

theory Triangle{
  //         C  gamma
  //        / \
  //       /   \
  //    b /     \ a
  //     /       \
  //    /         \
  //   A --------- B  beta
  //  alpha  c
  A: point
  B: point
  C: point

  a: (a:float, |- dist(B)(C) == a)
  b: (b:float, |- dist(C)(A) == b)
  c: (c:float, |- dist(A)(B) == c)

  alpha: float
  beta: float
  gamma: float
}

theory Similar{
  t1: Triangle
  t2: Triangle
}
similar_T: (t1: Triangle) -> (t2: Triangle) -> ()
