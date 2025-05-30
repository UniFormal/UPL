
//         A
//        / |
//       /  |
//      /   |
//     /    |
//    B --- C

theory OppositeLength {
    

    type point = (rat, rat, rat)
    type angle = rat

    //type float = rat
    type num = rat

    //alpha : angle = 0
    //beta : angle = 0
    //gamma : angle = 0

    // (a1, a2, a3)
    A : point
    // (b1, b2, b3)
    B : point
    // (b1, b2, ?)
    C : point

    tan = (x:angle ) -> { 0.0 }
    sqrt = (x:float) -> 0.0
    acos = (x:float) -> 0.0
    
    dist:_ = (a:point, b:point) -> sqrt(scalar(vector(a, b), vector(a, b)))
    scalar = (a:point, b:point) -> { return (a[0]+b[0], a[1]+b[1], a[2]+b[2]) }
    length = (a:point) -> { dist(a, (0,0,0)) }
    vector = (from:point, to:point) -> {return (b[0]-a[0], b[1]-a[1], b[2]-a[2])}
    getAngle = ( a:point, b:point, c:point) -> {
        ba : point = vector(b, a)
        bc : point = vector(b, c)
        acos(scalar(ba, bc) / (length(ba)*length(bc))) 
    }

    // right angle at C?
    theory rightAngleAtC {
        gamma : angle
        rightAngleC: |- gamma == 90
    }

    theory angleAtB {
        beta : angle
        betaAngle : |- getAngle(A, B, C) == beta
    }

    theory lengthBC {
        bc : num
        bcLength : |- dist(B, C)
    }

    theory angleSum {
        sum : |- alpha + beta + gamma == 180
    }

    theory OppositeLen {
        include rightAngleAtC
        include angleAtB
        include lengthBC

        ca : num
        ca : |- tan(beta) * bc

        // reicht so aus? ^
    }

    // t = TreeProblem {angleC = 80, ax = "geht noch nicht"}



}