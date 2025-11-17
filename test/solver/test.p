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
    ax3: |- a == a + 0

    ex: |- e == a-1


    bx: |- c == d - 1
    cx: |- c+2 == d+1
    
  }

  theory T2 {
    a: int
    b: int = 3
    c: int = 2

    ax: |- 1 * (c + a) == b
  }

  theory Ssa{
    a: float
    b: float
    gamma: float
  }


  theory Triangle {

    //         C  gamma
    //        / \
    //       /   \
    //    b /     \ a
    //     /       \
    //    /         \
    //   A-----------B  beta
    //  alpha  c


    a: float
    b: float
    c: float

    pi : float = 3.14

    alpha: float
    beta: float
    gamma: float

    //alphaGreater0: |- alpha > 0.0
    //betaGreater0: |- beta > 0.0
    //gammaGreater0: |- gamma > 0.0

    allAngles180 : |- alpha + beta + gamma == pi
    
    cosineLawAlpha : |- a^2 == b^2 + c^2 - 2*b*c*Math.cos(alpha)
    cosineLawBeta: |- b^2 == a^2 + c^2 - 2*a*c*Math.cos(beta)
    cosineLawGamma: |- c^2 == a^2 + b^2 - 2*a*b*Math.cos(gamma)

    sineLawAB: |- a/Math.sin(alpha) == b/Math.sin(beta)
    sineLawAC: |- a/Math.sin(alpha) == c/Math.sin(gamma)
    sineLawBC: |- b/Math.sin(beta) == c/Math.sin(gamma)
    
  }

  theory RightAngleTriangle {
    include Triangle

    rightAngleAtC : |- gamma == pi/2.0
    pythagoras : |- c^2 == a^2 + b^2

    sinAlpha: |- Math.sin(alpha) == a/c
    cosAlpha: |- Math.cos(alpha) == b/c
    tanAlpha: |- Math.tan(alpha) == a/b

    sinBeta: |- Math.sin(beta) == b/c
    cosBeta: |- Math.cos(beta) == a/c
    tanBeta: |- Math.tan(beta) == b/a

  }

  theory EqualSidedTriangle {
    include Triangle

    aEqualB : |- a == b
    bEqualC: |- b == c
    cEqualA: |- c == a

    alphaEqualBeta: |- alpha == beta
    betaEqualGamma: |- beta == gamma
    gammaEqualAlpha: |- gamma == alpha

    alpha60: |- alpha == pi/3.0
    beta60: |- beta == pi/3.0
    gamma60: |- gamma == pi/3.0
    //allAnglesEqual : |- (alpha == pi/3.0) & (beta == pi/3.0) & (gamma == pi/3.0)
  }

  theory Test {
    include Triangle

    ta: |- a == 4.0
    tb: |- b == 4.0
    tg: |- gamma == pi/2.0
  }

  theory Test2 {
    include Triangle

    a = 5.0
    b = 5.0
    gamma = pi/2.0
  }

  theory Test3 {
    //t: EqualSidedTriangle
    //t.a = 5.0
  }

  theory Test4 {
    include Triangle
    t = Ssa{a=5.0, b=5.0, gamma = Math.PI/2.0}
    a = t.a
    b = t.b
    gamma = t.gamma
  }
}