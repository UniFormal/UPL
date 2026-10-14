module similarTriangles_gameplay_example {
//The Background Theory declaring all relevant types and functions
type point
type triangle = (.point,.point,.point)
val dist : (.point -> (.point -> float))
val similar : (.triangle -> (.triangle -> bool))

theory SimilarTriangles {
  val _A : .point
  val _B : .point
  val _C : .point
  val _D : .point
  val _E : .point
  val _AB : float
  val _AB_P : |- .dist(_A)(_B) == _AB
  val _AC : float
  val _AC_P : |- .dist(_A)(_C) == _AC
  val _BE : float
  val _BE_P : |- .dist(_B)(_E) == _BE
  //val _are_similar : |- .similar((_A,_C,_D))((_A,_B,_E))
  val _CD : float = ((_AC * _BE) / _AB)
  val _CD_P : |- .dist(_C)(_D) == _CD = ???
  val _Theorem : |- _CD == ((_AC * _BE) / _AB) = ???
}

// ///
// The facts all have useful names. They certainly wouldn't be generated this way, so let's just claim the user can rename them.
// ///

theory Stage0 {
}
theory Stage1 {
  val tip : .point
}
theory Stage2 {
  val tip : .point
  val foot : .point
}
theory Stage3 {
  val tip : .point
  val foot : .point
  val ground : .point
}
theory Stage4 {
  val tip : .point
  val foot : .point
  val ground : .point
  val p : .point
  val q : .point
  val are_similar : |- .similar((tip, ground, foot))((p, ground, q)) = ???
  val apparent_height : int = 42
  val apparent_height_P : |- .dist(q)(p) == apparent_height = ???
  val ground_dist_small : int = 42
  val ground_dist_small_P : |- .dist(ground)(q) == ground_dist_small = ???
}
theory Stage5 {
  val tip : .point
  val foot : .point
  val ground : .point
  val p : .point
  val q : .point
  val are_similar : |- .similar((tip, ground, foot))((p, ground, q)) = ???
  val apparent_height : int = 42
  val apparent_height_P : |- .dist(q)(p) == apparent_height = ???
  val ground_dist_small : int = 42
  val ground_dist_small_P : |- .dist(ground)(q) == ground_dist_small = ???
  val ground_dist_large : int = 420
  val ground_dist_large_P : |- .dist(ground)(foot) == ground_dist_large = ???
}
theory Application {
  include .Stage5
  val _AC : int = ground_dist_large
  val _AB : int = ground_dist_small
  val _A : .point = ground
  val _are_similar : |- .similar((tip, ground, foot))((p, ground, q)) = are_similar
  val _B : .point = q
  val _BE : int = apparent_height
  val _C : .point = foot
  val _D : .point = tip
  val _E : .point = p
  val _AB_P : |- .dist(ground)(q) == ground_dist_small = ground_dist_small_P
  val _BE_P : |- .dist(q)(p) == apparent_height = apparent_height_P
  val _AC_P : |- .dist(ground)(foot) == ground_dist_large = ground_dist_large_P
  realize .SimilarTriangles
}
theory Stage6 {
  val tip : .point
  val foot : .point
  val ground : .point
  val p : .point
  val q : .point
  val ground_dist_small : int = 42
  val ground_dist_small_P : |- .dist(ground)(q) == ground_dist_small = ???
  val apparent_height : int = 42
  val apparent_height_P : |- .dist(q)(p) == apparent_height = ???
  val are_similar : |- .similar((tip, ground, foot))((p, ground, q)) = ???
  val ground_dist_large : int = 420
  val ground_dist_large_P : |- .dist(ground)(foot) == ground_dist_large = ???
  val height : float = ((ground_dist_large * apparent_height) / ground_dist_small)
  val height_P : |- .dist(foot)(tip) == height = ???
}
}

type point
type triangle = (.point,.point,.point)
val dist : (.point -> (.point -> float))
val similar : (.triangle -> (.triangle -> bool))


// Stage?0

module Stage0 {}

// Stage?1

module Stage1 {val tip : .point}

// Stage?2

module Stage2 {val tip : .point, val foot : .point}

// Stage?3

module Stage3 {
  val tip : .point
  val foot : .point
  val ground : .point
}

// Stage?4

module Stage4 {
  val tip : .point
  val foot : .point
  val ground : .point
  val p : .point
  val q : .point
  val are_similar : |- .similar((.Stage4.ground, .Stage4.foot, .Stage4.tip))((.Stage4.ground, .Stage4.q, .Stage4.p)) = ???
  val apparent_height : int = 36
  val apparent_height_P : |- .dist(.Stage4.q)(.Stage4.p) == .Stage4.apparent_height = ???
  val ground_dist_small : int = 50
  val ground_dist_small_P : |- .dist(.Stage4.ground)(.Stage4.q) == .Stage4.ground_dist_small = ???
}

// Stage?5

module Stage5 {
  val tip : .point
  val foot : .point
  val ground : .point
  val p : .point
  val q : .point
  val are_similar : |- .similar((.Stage5.ground, .Stage5.foot, .Stage5.tip))((.Stage5.ground, .Stage5.q, .Stage5.p)) = ???
  val apparent_height : int = 36
  val apparent_height_P : |- .dist(.Stage5.q)(.Stage5.p) == .Stage5.apparent_height = ???
  val ground_dist_small : int = 50
  val ground_dist_small_P : |- .dist(.Stage5.ground)(.Stage5.q) == .Stage5.ground_dist_small = ???
  val ground_dist_large : float = 48.25
  val ground_dist_large_P : |- .dist(.Stage5.ground)(.Stage5.foot) == .Stage5.ground_dist_large = ???
}

// C:\Users\silas\Documents\Uni\Git-Repos\UPL\test\FrameIt\Gameplay_Example\schema.p

theory SimilarTriangles {
  val _A : .point
  val _B : .point
  val _C : .point
  val _D : .point
  val _E : .point
  val _AB : float
  val _AB_P : |- .dist(_A)(_B) == _AB
  val _AC : float
  val _AC_P : |- .dist(_A)(_C) == _AC
  val _BE : float
  val _BE_P : |- .dist(_B)(_E) == _BE
  val _are_similar : |- .similar((_A, _C, _D))((_A, _B, _E))
  val _CD : float = ((_AC * _BE) / _AB)
  val _CD_P : |- .dist(_C)(_D) == _CD = ???
  val _Theorem : |- (_AB * _CD) == (_AC * _BE) = ???
}

// Stage?SchemaApplication

theory Application {
  val _AC : float = .Stage5.ground_dist_large
  val _AB : int = .Stage5.ground_dist_small
  val _A : .point = .Stage5.ground
  val _are_similar : |- .similar((.Stage5.ground, .Stage5.foot, .Stage5.tip))((.Stage5.ground, .Stage5.q, .Stage5.p)) = .Stage5.are_similar
  val _B : .point = .Stage5.q
  val _BE : int = .Stage5.apparent_height
  val _C : .point = .Stage5.foot
  val _D : .point = .Stage5.tip
  val _E : .point = .Stage5.p
  val _AB_P : |- .dist(.Stage5.ground)(.Stage5.q) == .Stage5.ground_dist_small = .Stage5.ground_dist_small_P
  val _BE_P : |- .dist(.Stage5.q)(.Stage5.p) == .Stage5.apparent_height = .Stage5.apparent_height_P
  val _AC_P : |- .dist(.Stage5.ground)(.Stage5.foot) == .Stage5.ground_dist_large = .Stage5.ground_dist_large_P
  realize SimilarTriangles
}

