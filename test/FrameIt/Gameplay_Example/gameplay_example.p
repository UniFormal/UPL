module similarTriangles_gameplay_example {
//The Background Theory declaring all relevant types and functions
type point
type triangle = (point,point,point)
dist: point -> point -> float
similar: triangle -> triangle -> bool
/////

theory InterceptTheorem_Scroll {
  //             D
  //           ,´|
  //          E  |
  //        ,´|  |
  //       A--B--C

  _A: point
  _B: point
  _C: point
  _D: point
  _E: point
  _AB: float
  _AB_P:  |- dist(_A)(_B) == _AB
  _AC: float
  _AC_P:  |- dist(_A)(_C) == _AC
  _BE: float
  _BE_P: |- dist(_B)(_E) == _BE
  _are_similar: |- similar((_D,_A,_C))((_E,_A,_B)) 
  __CD = _AC * _BE / _AB
  __CD_P: |- dist(_C)(_D) == __CD = ???
}

/////
// The facts all have useful names. They certainly wouldn't be generated this way, so let's just claim the user can rename them. 
/////

theory S1{
  //             tip
  //           ,´ |
  //          p   |
  //        ,´|   |
  //  ground--q--foot
  tip: point = ???
  foot: point = ???
  ground: point = ???
  p: point = ???
  q: point = ???
  ground_dist_small = 42
  ground_dist_small_P:  |- dist(ground)(q) == ground_dist_small = ???
  ground_dist_large = 420
  ground_dist_large_P:  |- dist(ground)(foot) == ground_dist_large = ???
  apparent_height = 42
  apparent_height_P: |- dist(q)(p) == apparent_height = ???
  are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???
}

theory Application1{
  include S1
  _AC = ground_dist_large
  _AB = ground_dist_small
  _A = ground
  _are_similar : |- .similar((tip, ground, foot))((p, ground, q)) = are_similar
  _B = q
  _BE = apparent_height
  _C = foot
  _D = tip
  _E = p
  _AB_P : |- .dist(ground)(q) == ground_dist_small = ground_dist_small_P
  _BE_P : |- .dist(q)(p) == apparent_height = apparent_height_P
  _AC_P : |- .dist(ground)(foot) == ground_dist_large = ground_dist_large_P
  realize InterceptTheorem_Scroll
}

/////
// To extract the result we need to actually apply the view induced by the equations above.
// This can be done in two ways:
/////

// 1) Create an instance of the application, and let the interpreter do it

Application1Inst = Application1{}

theory S2{
  include S1
  height = Application1Inst.__CD
  height_P = Application1Inst.__CD_P
}

// 2) Interpret the equations as substitution, because substitution into a term is composition

theory Application1Prime{ 
  // This is actually computed in place, replacing Application1
  height:_
  height_P:_
  include Application1
  // single underscore to avoid the declaration clash that couldn't happen if it were replaced
  _CD : float = ((ground_dist_large * apparent_height) / ground_dist_small)
  _CD_P : |- .dist(foot)(tip) == height = ???
}

// This is again "Substituted"

theory S2Prime{
  include S1
  height : float = ((ground_dist_large * apparent_height) / ground_dist_small)
  height_P : |- .dist(foot)(tip) == height = ???
}

test = S2{ }.height
}

module situation_buildup{
type point
type triangle = (point,point,point)
val dist : point -> point -> float
val similar : triangle -> triangle -> bool

theory Stage0 {
}

theory Stage1 {
  include .Stage0
  val B : point
}

theory Stage2 {
  include .Stage1
  val C : point
}

theory Stage3 {
  include .Stage2
  val D : point
}

theory Stage4 {
  include .Stage3
  val DC : float = 9.09000015258789
  val DC_P : |- dist(D)(C) == DC = ???
}
}