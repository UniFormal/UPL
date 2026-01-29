// A very simple and not quite trivial scroll, to test things
// Given two equal opaque points, the height of one is also the height of the other.
module minimal{
  type point
  height: point -> float = p -> 1
  P:point = ???
  Q:point = ???

  theory Pre{ // the Situation before applying the Scroll
    P: point
    Q: point
    E: |- P == Q 
    H: (x:float, |- height(P) == x) = (1,???) 
  } 

  theory _Scroll{
    p1: point
    p2: point
    h1: (x:float, |- height(p1) == x)
    h2: (x:float, _) = (h1(1) * 2, ???)
  }

  theory Post{
    include Pre
    realize _Scroll
    p1 = P
    p2 = Q
    h1 = H
    t = _Scroll{ p1 = P, p2 = Q, h1 = H }
  } 

  test = Post{  P = ???   Q = ???   E = ???}.h2(1)
}

module variants{
  // Code that wastes space in `minimal` rn, but I may want again later

  type point
  height: point -> float = p -> 1
  P:point = ???
  Q:point = ???

  theory Pre{ // the Situation before applying the Scroll
    P: point
    Q: point
    E: |- P == Q 
    H: (x:float, |- height(P) == x) = (1,???) 
  } 
  theory _Scroll{
      p1: point
      p2: point
      h1: float
      h1_def: |- height(p1) == h1
      h2 = h1 * 2
      h2_def: |- height(p2) == h2
  }
  module v4{ 
    theory _Scroll_Gen{
      p1: point
      p2: point
      h1: (x:float, |- height(p1) == x)
      h2: (x:float, _) = (h1(1) * 2, ???)
    }

    theory Scroll_Appl{
      include Pre
      type Scroll_inst = _Scroll_Gen{ p1 = P,  p2 = Q}
      scroll : Scroll_inst
      //h = scroll{h1 = H}.h2(2)
    }

  }

  // V3 Instantiate the Scroll through substitution
  // It's not possible to do the kind of substitution I would like in UPL, so it has to be done via Meta Magic
  module v3{ 
    theory _Scroll_Gen{
      p1: point
      p2: point
      theory Inst{
        h1: (x:float, |- height(p1) == x)
        h2: (x:float, _) = (h1(1) * 2, ???)
      }
    }

    // Intention:
    //type i0 = _Scroll_Gen{ p1=P, p2=Q }.Inst
    // i1 = _Scroll_Gen{ p1=P, p2=Q } 
    // type i2 = i1.Inst

    //t:i2 = _

    // Not possible => Meta Magic
    theory _Scroll_Instance{
      include Pre
      h1: (x:float, |- height(P) == x)
      h2: (x:float, |- height(Q) == x) = (h1(1) * 2, ???)
    }

    theory Scroll_Appl{
      include Pre
      realize _Scroll_Instance
      h1 = H
    }

    theory Post{
      h2 = Scroll_Appl{P = P  Q = Q  E = E}.h2
    }

    test = Post{P = P  Q = Q }.h2
  }

  // V2 Bind all variables
  // Kinda works. Two problems remain
  // - instantiation of Facts only via `???` (Or fruitless circumnavigation)
  // - if every term appearing in a proof-type is locally bound they cannot be shared between declarations.
  //   => either just one big dependent function, or information is lost
  module v2 { 
    theory _Scroll{
      h1: (y:float, p1: point, p2: point, |- p1 == p2, |- height(p1) == y) 
      p2: point
      // val p2 = bound p2 is not expressible
      h2: (x:float, |- height(p2) == x) = (h1(1)*2, ???)
    }

    theory Post{
      P: point
      Q: point
      E: |- P == Q 
      H: (x:float, |- height(P) == x) = (1,???)

      realize _Scroll
      h1 = (H(1),P,Q,E,H(2))
      p2 = Q
    }

    test = Post{  P = P   Q = Q   E = ???}.h2(1)
  }

  module v1{

    theory Post{
      include Pre
      theory _Scroll{
        h1: (x:float, |- height(P) == x)
        h2 = h1(1) * 2
      }
      test1:_ = _Scroll{h1 = H}
    }
  }

}