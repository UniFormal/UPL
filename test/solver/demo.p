module Demo{
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

theory TestOppositeLength {
    include RightAngleTriangle

    c = 5.0
    beta = Math.PI/3.0
    gamma = Math.PI/2.0
  }

//////////////////////////////////////////////////////

theory OppositeLength{
    // Fields
    a: float
    beta: float
    gamma: float
    b: float
    
    // Axioms
    tangent : |- Math.tan(beta) == b/a
    rightAngle : |- gamma == Math.PI/2
    
    // Measurements
    a = 5.0
    beta = Math.PI/3.0
    gamma = Math.PI/2.0
}

/////////////////////////////////////////////////////

theory TestInterceptTheorem2 {
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