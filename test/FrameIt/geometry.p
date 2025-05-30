module geometry{

  type num = rat 
  // most numbers here are not actually rational, so a type alias to allow for quick switching later

  type vec = (num, num, num)
  type point = vec
  type ray = (point, vec)
  
  vectorFromTo: point -> point -> vec 
    = p -> q -> (q(1)-p(1), q(2)-p(2), q(3)-p(3))

  scalarProd: vec -> vec -> num
    = v -> w -> v(1)*w(1) + v(2)*w(2) + v(3)*w(3)

  sqrt: num -> num 

  acos: num -> num 

  tan: num -> num 

  length: vec -> num 
    = v -> sqrt( v(1)*v(1) + v(2)*v(2) + v(3)*v(3) )

  distance: point -> point -> num
    = p -> q -> length(vectorFromTo(p)(q))
    
  angle: point -> point -> point -> num
    = a -> b -> c -> {
      val ba = vectorFromTo(b)(a)
      val bc = vectorFromTo(b)(c)
      acos( scalarProd(ba)(bc) / (length(ba) * lenght(bc)) )
    }

  rightangle: point -> point -> point -> bool
    ={
      val 
    }
  

  // Assumed Triangle Layout
  // 
  //       A
  //      /|
  //     / |
  //    /  |
  //   /___|
  //  B    C


  theory Triangle{
    a: point
    b: point
    c: point
  }

  theory Angle{
    p1: point
    vertex: point
    p2: point
    side1: ray
      = (vertex, vectorFromTo(vertex)(p1))
    side2: ray
      = (vertex, vectorFromTo(vertex)(p2))

    angleMeasure: num = angle(a)(b)(c)
  }

  theory RightTrinangle_AtC{
    include Triangle
    rightAngleAtC: _ = angle(a)(c)(b) == 90
  }  

  theory AngleAtA{
    include Triangle
    angleAtA: (angle: num , |- angle(b)(a)(c) == angle)
  }

  theory AngleAtB{
    include Triangle
    isAngleAtB : (angleAtB : num, |- angle(a)(b)(c) == angleAtB)
  }

  theory OppositeLenghtScroll{
    include Triangle
    include AngleAtB
    rightAngleAtC : |- angle(a)(c)(b) == 90
    distanceBC : num
    isDistanceBC: |- length(vectorFromTo(b)(c)) == distanceBC
    
    // Solution
    deducedLineCA: num = {
      if(isDistanceBC && isAngleAtB) {
        return (tan(angleAtB) * distanceBC)
      }
      -1
      }
  }

  theory OpLen{
    include Triangle
    beta: angle(A)(B)(C)
    gamma: rightangle(B)(C)(A)
    distanceBC : num
    isDistanceBC: |- length(vectorFromTo(b)(c)) == distanceBC
    
    // Solution
    deducedLineCA: num = {
      if(isDistanceBC && isAngleAtB) {
        return (tan(angleAtB) * distanceBC)
      }
      -1
      }
  }

  theory Point{
    x: num
    y: num
    z: num
  }


  //////////////////////////////////////////////////
  // Dummys
  //////////////////////////////////////////////////


  test_a=(0,0,0) 
  test_b=(1,2,3)
  test_c=(1,1,1)

  mytriangle = Triangle{a= test_a, b= test_b, c= test_c}
  p= angle(test_a)(test_b)(test_c)
  p1 = Point{x=0}
}
