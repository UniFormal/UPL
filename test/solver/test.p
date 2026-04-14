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

    alpha: float
    beta: float
    gamma: float

    //alphaGreater0: |- alpha > 0.0
    //betaGreater0: |- beta > 0.0
    //gammaGreater0: |- gamma > 0.0

    allAngles180 : |- alpha + beta + gamma == Math.PI
    
    cosineLawAlpha : |- a^2 == b^2 + c^2 - 2*b*c*Math.cos(alpha)
    cosineLawBeta: |- b^2 == a^2 + c^2 - 2*a*c*Math.cos(beta)
    cosineLawGamma: |- c^2 == a^2 + b^2 - 2*a*b*Math.cos(gamma)

    sineLawAB: |- a/Math.sin(alpha) == b/Math.sin(beta)
    sineLawAC: |- a/Math.sin(alpha) == c/Math.sin(gamma)
    sineLawBC: |- b/Math.sin(beta) == c/Math.sin(gamma)
    
  }

  theory RightAngleTriangle {
    include Triangle

    rightAngleAtC : |- gamma == Math.PI/2.0
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

    alpha60: |- alpha == Math.PI/3.0
    beta60: |- beta == Math.PI/3.0
    gamma60: |- gamma == Math.PI/3.0
    //allAnglesEqual : |- (alpha == Math.PI/3.0) & (beta == Math.PI/3.0) & (gamma == Math.PI/3.0)
  }

  theory Test {
    include Triangle

    ta: |- a == 4.0
    tb: |- b == 4.0
    tg: |- gamma == Math.PI/2.0
  }

  theory Test2 {
    include Triangle

    c = 5.0
    alpha = Math.PI/6.0
    beta = Math.PI/3.0
    gammaPI: |- gamma == Math.PI/2.0
  }

  

  theory Test3 {
    a: float
    ax: |- 2 ^ a == 8
  }

  theory Test4 {
    include Triangle
    t = Ssa{a=5.0, b=5.0, gamma = Math.PI/2.0}
    a = t.a
    b = t.b
    gamma = t.gamma
  }

  theory Test5 {
    include EqualSidedTriangle
    a = 5.0
  }

  theory Test6 {
    //t: EqualSidedTriangle
    //t.a = 5.0
  }

  theory Test7 {
    //x: float = 0.0 // NumberType float
    //t = Triangle{a=5.0, b=???, gamma=Math.PI/2.0, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???, beta=Math.PI/4.0, alpha=???, c=???}
    // ClassType SolverTest.Triangle
    r = RightAngleTriangle{a=5.0, b=???, gamma=Math.PI/2.0, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???, beta=Math.PI/4.0, alpha=???, c=???, rightAngleAtC=???, pythagoras=???, sinAlpha=???, cosAlpha=???, tanAlpha=???, sinBeta=???, cosBeta=???, tanBeta=???}
     b = 20.0
  }

  theory Test8 {
    t1 = Triangle{a=5.0, b=5.0, gamma=Math.PI/2.0, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???, beta=???, alpha=???, c=???}
    t2 = RightAngleTriangle{a=2.0, b=2.0, gamma=???, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???, beta=???, alpha=???, c=???,
      rightAngleAtC=???, pythagoras=???, sinAlpha=???, cosAlpha=???, tanAlpha=???, sinBeta=???, cosBeta=???, tanBeta=???}
    //t2.gamma = Math.PI/2.0
  }

  theory TestOppositeLength {
    include RightAngleTriangle

    a = 5.0
    beta = Math.PI/6
  }

  theory InterceptTheorem {
    t1 : Triangle
    t2 : Triangle

    alphaEqual:|- t1.alpha == t2.alpha
    betaEqual:|- t1.beta == t2.beta
    gammaEqual:|- t1.gamma == t2.gamma

    ratioAB:|- t1.a/t1.b == t2.a/t2.b
    ratioAC:|- t1.a/t1.c == t2.a/t2.c
    ratioCB:|- t1.c/t1.b == t2.c/t2.b
  }

  theory TestInterceptTheorem {
    // TODO Triangle ist OpenRef?? 
    include InterceptTheorem

    t1 = Triangle{a=4.0, b=2.0, gamma=Math.PI/2.0, beta=???, alpha=???, c=???, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???}
    t2 = Triangle{a=20.0, b=???, gamma=Math.PI/2.0, beta=???, alpha=???, c=???, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???}
    
    //alphaEqual:|- t1.alpha == t2.alpha
    //betaEqual:|- t1.beta == t2.beta
    //gammaEqual:|- t1.gamma == t2.gamma

    //ratioAB:|- t1.a/t1.b == t2.a/t2.b
    //ratioAC:|- t1.a/t1.c == t2.a/t2.c
    //ratioCB:|- t1.c/t1.b == t2.c/t2.b
  }

  theory TestInterceptTheorem2 {
    //include InterceptTheorem

    t1 = Triangle{a=4.0, b=2.0, gamma=Math.PI/2.0, beta=???, alpha=???, c=???, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???}
    t2 = Triangle{a=20.0, b=???, gamma=Math.PI/2.0, beta=???, alpha=???, c=???, sineLawBC=???, sineLawAC=???, sineLawAB=???, cosineLawGamma=???, cosineLawBeta=???, cosineLawAlpha=???, allAngles180=???}
    
    alphaEqual:|- t1.alpha == t2.alpha
    betaEqual:|- t1.beta == t2.beta
    gammaEqual:|- t1.gamma == t2.gamma

    ratioAB:|- t1.a/t1.b == t2.a/t2.b
    ratioAC:|- t1.a/t1.c == t2.a/t2.c
    ratioCB:|- t1.c/t1.b == t2.c/t2.b
  }
}

