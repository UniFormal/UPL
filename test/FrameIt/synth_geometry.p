module synth_geometry_v2{
// #begin "Library" : Just a bunch of stubs, until there are actual importable implementations
    type num = rat
    type vec = (num, num, num)
    type coordinate
    X: coordinate
    Y: coordinate
    Z: coordinate

    scalarProd: vec -> vec -> num
    = v -> w -> v(1)*w(1) + v(2)*w(2) + v(3)*w(3)

    sqrt: num -> num 
    acos: num -> num 
    tan: num -> num 
// #end "Library" 

    theory Point{
        x: num?
        y: num?
        z: num?
        vecTo: Point -> vec = q -> (q.x-x, q.y-y, q.z-z)
    }

    type point = (num, num, num)
    type known1 = (p: point, coordinate: int[0;2], value: num, |- p(coordinate) == value )

    known: (point, coordinate) -> bool

    is: (n: num, m: num) -> |- n == m

    vectorFromTo: Point -> Point -> vec 
    = p -> q -> (q.x-p.x, q.y-p.y, q.z-p.z)

    
    refl: (a: any) -> |- a == a

    length: vec -> num
    = v -> sqrt(scalarProd(v)(v))

    sameDirection: vec -> vec -> bool
    = v -> w -> {
        val lambda_1 = v(1) / w(1)
        val lambda_2 = v(2) / w(2)
        val lambda_3 = v(3) / w(3)
        lambda_1 == lambda_2 & lambda_2 == lambda_3
    }

    theory Line{
        p_1	: Point
        p_2 : Point
    }

    theory Ray{
        from: Point
        direction: vec
    }

    theory Distance{
        from: Point
        to: Point
        dist: num
    }

    theory Angle{
        side1: Ray
        side2: Ray
        hasVertex: |- side1.from == side2.from 

        vertex: Point = side1.from
        angle: num
         = {
            s1 = side1.direction
            s2 = side2.direction
            acos( scalarProd(s1)(s2) / (length(s1) * length(s2)) )
            }
    }

    pendulum : Point -> _ 
        = po -> {
            p:_ = Point{x= po.x, y= po.y, z=0}
            isZero:_ = p.z == 0
            (p, isZero )
            }

    protractor = (p:Point) -> (v: vec) -> (w: vec) -> 
        Angle{side1=Ray{from=p, direction=v}, side2=Ray{from=p, direction=w}, hasVertex = refl(p)}

    opLen: (a: Point) -> (b: Point) -> |- b.z == 0 -> Point
    = a -> b -> {
        ax: _ = a.x
        ay: _ = a{y}
        c: Point = pendulum(a)
        gamma = protractor(c)(b.vecTo(c))
        _
    }
    
    test: _ = {
        p_1: _ = Point{x=0, y=0, z=0}
        p_2: Point = p_1
        p_3: Point = pendulum(p_1)
        p_4: point = (5,2,3)
        p_1.x
        p_3.z
        k: _ = (p_4, 1, 5 , refl(5))
    }

    isRightangle: (a: Angle) -> |- a.angle == 90 -> Rightangle{theAngle = a}
}