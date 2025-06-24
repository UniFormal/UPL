module SolverTest {
  theory T {
    a: int
    b: float = 1.0
    c = 2
    d = 3
    e: int

    x: int = 4
    y: int = x

    ax: |- a == 2 * c
    ax2: |- d + 1 == a
    ax3: |- a + 4 == a * 2

    ex: |- e == a-1


    bx: |- c == d - 1
    cx: |- c+2 == d+1
    
  }

  theory MathStubs {
    cos : float -> float
    sqrt : float -> float
  }

  theory Triangle {
    include MathStubs

    // StackOverflowException???

    a: float
    b: float
    c: float

    pi : float = 3.14

    alpha: float
    beta: float
    gamma: float

    allAngles180 : |- alpha + beta + gamma == pi
    
    cosineLawAlpha : |- a^2 == b^2 + c^2 - 2*b*c*cos(alpha)
    
  }

  theory RightAngleTriangle {
    include Triangle

    //rightAngleAtC : |- gamma == 90
    //pythagoras : |- a*a + b*b == c*c


  }

  theory EqualSidedTriangle {
    include Triangle

    //allSidesEqual : |- (a == b) && (a == c)
    //allAnglesEqual : |- (alpha == 60) && (beta == 60) && (gamma == 60)
  }
}