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

  theory MathStubs {
    sin: float -> float = x -> x
    cos : float -> float = x -> x
    tan: float -> float = x -> x

    sqrt : float -> float = x -> x
  }

  theory Triangle {
    include MathStubs

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
    
    cosineLawAlpha : |- a^2 == b^2 + c^2 - 2*b*c*cos(alpha)
    cosineLawBeta: |- b^2 == a^2 + c^2 - 2.0*a*c*cos(beta)
    cosineLawGamma: |- c^2 == a^2 + b^2 - 2*a*b*cos(gamma)

    sineLawAB: |- a/sin(alpha) == b/sin(beta)
    sineLawAC: |- a/sin(alpha) == c/sin(gamma)
    sineLawBC: |- b/sin(beta) == c/sin(gamma)
    
  }

  theory RightAngleTriangle {
    include Triangle

    rightAngleAtC : |- gamma == pi/2.0
    pythagoras : |- c^2 == a^2 + b^2

    sinAlpha: |- sin(alpha) == a/c
    cosAlpha: |- cos(alpha) == b/c
    tanAlpha: |- tan(alpha) == a/b

    sinBeta: |- sin(beta) == b/c
    cosBeta: |- cos(beta) == a/c
    tanBeta: |- tan(beta) == b/a

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
}