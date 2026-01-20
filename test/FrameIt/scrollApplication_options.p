module Monday{
type point

///////
// V1
// Basic UPL, no big changes
// Measurements have two components, both have their own declaration e.g.
//   distPQ: float = 42
//   distPQ_construction: |- distPQ == dist(P,Q)
// [fact]_construction always has that structure
///////
theory Situation {
  p1: point // unknown coordinates
  p2: point
  p3: point
  angle1: float = ... // measured value
  angle1_construction: |- angle1 == angle(p1,p2,p3) // axiom capturing construction of the value
  angle2: float
  angle2_construction: |- angle1 == angle(p2,p1,p3)
  dist1: float = ... // measured value
  dist1_construction: |- dist1 == dist(p1,p2)
}

///////
// V2 
// ExprDecl can hold an "actual" value, as well as their definiens, written
// `name : type = definiens => value`
// the value can be used to deal with situations where 
// - computing the definiens is infeasible, e.g. kryptographic trapdoor functions, or FrameIT measurements, or  
// - the definiens is an important part of a variables semantics, even if the value is known 
///////

theory Situation3 {
  p1: point // unknown coordinates
  p2: point
  p3: point
  angle1: float = angle(p1,p2,p3) //=> (measured value)
  angle2: float = angle(p2,p1,p3) //=> (measured value)
  dist1: float = dist(p1,p2) //=> (measured value)
}

///////
// V3
///////

theory Situation4 {
  p1: point // unknown coordinates
  p2: point
  p3: point
  angle1: the angle(p1,p2,p3) //= (measured value)
  dist1:  the dist(p1,p2) //= (measured value)
  angle2: the angle(p2,p1,p3) //= (measured value)
  // alternatively if the user confirmed right angle instead of measuring
  rightangle: _ = ???
  p1p2_right: |- rightangle(angle2)
}

theory Scroll4 {
  bottom: point
  top: point
  observer: point
  observer_angle: the angle(top,observer,bottom)
  observer_distance: the dist(observer,bottom)
  right_angle: |- rightangle(angle(top,bottom,observer))
  height: the dist(bottom,top) = observer_distance * tan(observer_angle)
}

theory Scroll4Apllication_as_built {
  include Situation4
  include Scroll4
  bottom = p1
  top = p2
  observer = p3
  observer_angle = angle1
  observer_distance = dist1
  right_angle = p1p1_right
}

theory Scroll4Apllication_as_flattened_and_simplified {
  include Situation4
  realize Scroll4
  bottom = p1
  top = p2
  observer = p3
  observer_angle = angle1
  observer_distance = dist1
  right_angle = (trueI infered after calcuation) // alternatively: p1p2_right
  height: the dist(bottom,top) = (calculated value)
}


theory Scroll3 {
  bottom: point
  top: point
  observer: point
  observer_angle = angle(top,observer,bottom)
  observer_distance = dist(observer,bottom)
  right_angle: |- rightangle(angle(top,bottom,observer))
  height = dist(bottom,top)
  height_def: |- height == observer_distance * tan(observer_angle)
}

theory Scroll2 {
  a: float
  b: float
  c: float
  alpha: float
  beta: float
  gamma: float
  // triangle axioms
}

theory Scroll2Application {
  include Situation
  include Scroll2
  a = dist1
  alpha = angle1
  beta = angle2
}

theory Scroll1 {
  bottom: point
  top: point
  observer: point
  observer_angle: float
  observer_angle_def: |- observer_angle == angle(top,observer,bottom)
  observer_distance: float
  observer_distance_def: |- observer_distance == dist(observer,bottom)
  right_angle: |- rightangle(angle(top,bottom,observer))
  height = observer_distance * tan(observer_angle)
  height_def: |- height == dist(bottom,top) = ???
}

theory Scroll1Application_as_Built {
  include Situation
  realize Scroll
  bottom = p1
  top = p2
  observer = p3
  observer_angle = angle1
  observer_distance = dist1
}

theory Scroll1Application_as_flattened_internally {
  include Situation
  realize Scroll
  bottom = p1
  top = p2
  observer = p3
  observer_angle = angle1
  observer_distance = dist1
  // automatically found proofs
  observer_angle_def = angle1_construction
  observer_distance_def = observer_distance_def
  right_angle = ... // requires some calculation
  height = ... // calculated value
  height_def: |- height == dist(bottom,top)
}

theory Scroll1_bigstep {
  bottom: point
  top: point
  observer: point
  observer_angle: float
  observer_angle_def: |- observer_angle == angle(top,observer,bottom)
  observer_distance: float
  observer_distance_def: |- observer_distance == dist(observer,bottom)
  right_angle: |- rightangle(angle(top,bottom,observer))

  height: float
  height_def: |- height == dist(bottom,top)
  // same for other values of the triangle like topangle, distance_to_top
  ...

  // all other triangle laws
  height_by_tan: |- height = observer_distance * tan(observer_angle)
  ...

}

theory Scroll1_bigstep_Application_as_Built {
  include Situation
  include Scroll
  bottom = p1
  top = p2
  observer = p3
  observer_angle = angle1
  observer_distance = dist1
  observer_angle_def = ???
  observer_distance_def = ???
  
  // other fields
}

theory Scroll1_bigstep_Application_as_solved {
  include Situation
  include Scroll
  bottom = p1
  top = p2
  observer = p3
  observer_angle = angle1
  observer_distance = dist1
  height = ... // solved value
  
  // other fields
}

}