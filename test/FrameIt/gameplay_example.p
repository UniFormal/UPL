module treeWorld_example{

tan: float -> float

theory BackgroundTheory{
  type point
  dist: point -> point -> float
  angle: point -> point -> point -> float
  height: point -> float
  pos: point -> (float,float)
  //ground: (P: point, Q: point) -> (|- pos(P) == pos(Q)) -> (|- (dist(P,Q)) == (height(P) - height(Q)))
}

theory S1{
  include BackgroundTheory
  A: point
  B: point
}

theory S2{
  include S1
  C: point
  A: point
  CGrounded: |- height(C) == 0.0
  CuA: 		|- pos(A) == pos(C)
}

theory S3{
  include S2
  BC: |- dist(B)(C) == 0.815
  ABC: |- angle(A)(B)(C) == 45.0
  BCA: |- angle(B)(C)(A) == 90.0
}

theory OpLen_Scroll{
  include BackgroundTheory
  _A: point
  _B: point
  _C: point
  _RA_C: |- angle(_B)(_C)(_A) == 90.0
  _Beta: float
  _AngleAtB: |- angle(_A)(_B)(_C) == _Beta
  _Dist_BC: float
  _BC: |- dist(_B)(_C) == _Dist_BC

  __CA: |- dist(_C)(_A) == tan(_Beta) * _Dist_BC
  //=~ dist(C,A) === (dist(C,A) / dist(B,C)) * dist(B,C)
}

theory Slots{
  include S3
  include OpLen_Scroll
  _A = A
  _B = B
  _C = C
  _Beta = 45.0
  _Dist_BC = 0.815
  // UPL currently can't handle those assignments
  //_AngleAtB = ABC
  //_RA_C = BCA
  //_BC = BC
}

theory S4{
  include S3
  CA: |- dist(C)(A) == 0.815
  hA: |- height(A) == 0.815
}
}