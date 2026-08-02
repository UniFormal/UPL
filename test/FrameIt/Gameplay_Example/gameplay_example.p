module similarTriangles_gameplay_example {
//The Background Theory declaring all relevant types and functions
type point
type triangle = (point,point,point)
dist: point -> point -> float
similar: triangle -> triangle -> bool
// ///

theory SimilarTriangles{
  //             D
  //           ,´|
  //          E  |
  //        ,´|  |
  //       A--B--C

  A: point
  B: point
  C: point
  D: point
  E: point
  AB: float
  AB_P:  |- dist A B == AB
  AC: float
  AC_P:  |- dist A C  == AC
  BE: float
  BE_P: |- dist B E  == BE
  are_similar: |- similar ((D,A,C)) ((E,A,B)) 

  // The solution of the scroll. Recognizable by 
  // - starting with a double underscore
  // - having a definiens ?
  CD = AC * BE / AB
  CD_P: |- dist C D == CD = ???
  // CD_Schema: |- CD == (_AC * _BE / _AB) = ???
}

// ///
// The facts all have useful names. They certainly wouldn't be generated this way, so let's just claim the user can rename them. 
// ///

theory Stage1{
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
  ground_dist_small = 21
  ground_dist_small_P:  |- dist ground q == ground_dist_small = ???
  ground_dist_large = 420
  ground_dist_large_P:  |- dist ground foot == ground_dist_large = ???
  apparent_height = 21
  apparent_height_P: |- dist q p == apparent_height = ???
  are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???
}

theory Application_raw {
  include Stage1
  A = ground
  AB = ground_dist_small
  B = q
  AC = ground_dist_large
  C = foot
  BE = apparent_height
  D = tip
  E = p
  BE_P : |- dist(q)(p) == apparent_height = apparent_height_P
  AB_P : |- dist(ground)(q) == ground_dist_small = ground_dist_small_P
  AC_P : |- dist(ground)(foot) == ground_dist_large = ground_dist_large_P
  realize SimilarTriangles
}

theory Application_solved {
  tip : .point = ???
  foot : .point = ???
  ground : .point = ???
  p : .point = ???
  q : .point = ???
  ground_dist_small : int = 42
  ground_dist_small_P : |- .dist(ground)(q) == ground_dist_small = ???
  ground_dist_large : int = 420
  ground_dist_large_P : |- .dist(ground)(foot) == ground_dist_large = ???
  apparent_height : int = 42
  apparent_height_P : |- .dist(q)(p) == apparent_height = ???
  are_similar : |- .similar((tip, ground, foot))((p, ground, q)) = ???
  height : float = ((ground_dist_large * apparent_height) / ground_dist_small)
  height_P : |- .dist(foot)(tip) == height = ???
}

theory Stage2{
  include Stage1
  height : float = ((ground_dist_large * apparent_height) / ground_dist_small)
  height_P : |- .dist(foot)(tip) == height = ???
}

test = Stage2{ }.height
}