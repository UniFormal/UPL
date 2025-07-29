module synth_geometry_v1 {
// #begin "Library" : Just a bunch of stubs, until there are actual importable implementations
    type num = rat
    type vec = (num, num, num)

    sqrt: num -> num 
    acos: num -> num 
    tan: num -> num 
// #end "Library" 

    theory Point{}
// #begin PointHierarchy : There are 2^3 possibe combinations of known coordinates.

    theory Point_x{
        include Point
        x: num
    }

    theory Point_y{
        include Point
        y: num
    }

    theory Point_z{
        include Point
        z: num
    }

    theory Point_xy{
        include Point_x
        include Point_y
    }

    theory Point_xz{
        include Point_x
        include Point_z
    }

    theory Point_yz{
        include Point_y
        include Point_z
    }

    theory Position{
        include Point_xy
        include Point_xz
        include Point_yz
    }
    
// #end PointHierarchy
    
    refl: (p: Point) -> |- p == p

    scalarProd: vec -> vec -> num
    = v -> w -> v(1)*w(1) + v(2)*w(2) + v(3)*w(3)

    length: vec -> num 
    = v -> sqrt(scalarProd(v)(v))

    sameDirection: vec -> vec -> bool
    = v -> w -> {
        val lambda_1 = v(1) / w(1)
        val lambda_2 = v(2) / w(2)
        val lambda_3 = v(3) / w(3)
        lambda_1 == lambda_2 & lambda_2 == lambda_3
    }
    theory Abstract_Line{
        p_1	: Point
        p_2 : Point
    }

    theory Line{
        p_1	: Position
        p_2 : Position
    }
    
    vectorFromTo: Position -> Position -> vec 
    = p -> q -> (q.x-p.x, q.y-p.y, q.z-p.z)

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
        vertex: Point
        side1: vec
        side2: vec
        //vertex: |- side1.from == side2.from 
        angle: num
         = {
            acos( scalarProd(side1)(side2) / (length(side1) * length(side2)) )
            }
    }

    pendulum : Point_xy -> _ 
        = po -> Position{x= po.x, y= po.y, z=0}

    protractor = (p:Point) -> (v: vec) -> (w: vec) -> 
        Angle{side1=v, side2=w, vertex = p}

    sgrjpi = (r: Ray) -> (s:Ray{from=r.from}) -> {
        val v = r.direction
        val w = s.direction
        val p = r.from
        Angle{side1=v, side2=w, vertex = p}
    }

    opLen: (a: Point_xy) -> Position{z=0} -> Position//{include Point_xy = a}
    = a -> b -> {
        ax: _ = a.x
        ay: _ = a{y}
        c: Position = pendulum(a)
        gamma = protractor(c)(vectorFromTo(b)(c))
        _
    }
    
    test: _ = {
        p_1: _ = Point_xy{x=1, y=0}
        p_2 : Point = p_1
        p_3: Position{z=0} = pendulum(p_1)
        p_1.x
        p_3.z
    }

    isRightangle: (a: Angle) -> |- a.angle == 90 -> Rightangle{theAngle = a}
}

module synth_geometry_Venema{
// Synthetic Geometry as per "The foundations of geometry" Venema_2011
// Mod(mod(Vector,length=n).u)

    theory Neutral_Geometry{
        // Preliminary assumptions: There are classical reals and sets
        type num = rat
        in: point -> set[point] -> bool

        type point
        type line = [point]
        
        theory On{
            l: line
            theory Point{
                p: point
                on: |- in(p)(l)
            }
        }

        on: On{l=l_1}.Point
        incidenceAxiom: (p:point) -> (q:point) -> (l:line, |- in(p)(l), |- in(q)(l) )
        type distance = point -> point -> num
    }
    
    theory Incidence_Geometry{
        // Primitives
        type Point
        type Line
        on: (Point, Line) -> bool // Not quite happy with this implementation of a "predicate type family", but I cannot see a better solution rn
        //type On = (p: Point, l: Line) -> |- on(p,l)

        // Axioms
        // Incidence Axiom 1. For every pair of distinct points `p` and `q` there exists exactly one line `l` such that both `p` and `q` lie on `l`.
        incidenceAxiom1: (p:Point, q:Point, |- p!=q) -> (l: Line, |- on(p,l), |- on(q,l), ((l2:Line) -> (|- on(p,l2)) -> (|- on(q,l2)) -> (|- l2==l)))
        // Incidence Axiom 2. For every line `l` there exist at least two distinct points `p` and `q` such that both `p` and `q` lie on `l`.
        incidenceAxiom2: (l: Line) -> (p: Point, q: Point, |- on(p,l), |- on(q,l))
        // Incidence Axiom 3. There exist three points that do not all lie on any one line.
        incidenceAxiom3: (
            p: Point, q: Point, r: Point, 
            (l: Line) -> |- (!on(p,l) | !on(q,l)) | !on(r,l)
            )
        // Equivalent: There is a line, and for all lines there is a point that does not lie on it
        // incidenceAxiom31: (_: Line, (l: Line) -> (p:Point, |- !on(p,l)))

        // Definition 2.2.1. Three points A, B, and C are collinear if there exists one line l such that all three of the points A, B, and C all lie on l.
        type _collinear = (A: Point, B: Point, C: Point, l: Line, |- on(A,l), |- on(B,l), |- on(C,l))

        theory collinear{
            A: Point
            B: Point
            C: Point
            coll: (l: Line, |- on(A,l), |- on(B,l), |- on(C,l))
        } 

        // Definition 2.3.1. Two lines l and m are said to be parallel if there is no point P such that P lies on both l and m.
        type _parallel = (l: Line, m: Line) 
            -> (P:Point) -> (|- !on(P,l) | !on(P,m)) 

        theory parallel{
            l: Line
            m: Line
            par: (P:Point) -> (|- !on(P,l) | !on(P,m))
        }
        // There is no `empty` type, so no standard negation 
        type notParallel = (l:Line, m: Line) 
            -> (P:Point, |- on(P,l) , |- on(P,m)) 
        
        // Definition 2.6.1. Two lines are said to intersect if there exists a point that lies on both lines.
        type intersect = (l: Line, m: Line)
            -> (p: Point, |- on(p,l), |- on(p,m))

        // Theorem 2.6.2. if l and m are distinct nonparallel lines, then there exists a unique point P such that P lies on both l and m.
        theorem_262: (l: Line, m: Line)
            -> ((|- ! l == m), notParallel(l,m)) 
            -> (p:Point, |- on(p,l), |- on(p,m), 
                (q: Point, |- on(q,l), |- on(q,m)) 
                    -> |- p==q 
                )
        = (l, m) -> _ -> _
    }

    // Definition 2.2.1. Three points A, B, and C are collinear if there exists one line l such that all three of the points A, B, and C all lie on l.
    theory collinear{
        include Incidence_Geometry
        // This is a hacky type-family. 
        // the "actual" type defined here is collinear(A,B,C). 
        type collinear = (A: Point, B: Point, C: Point) 
            -> (l: Line, |- on(A,l), |- on(B,l), |- on(C,l))
    }

    //Definition 2.3.1. Two lines l and m are said to be parallel if there is no point P such that P lies on both l and m.
    theory parallel{
        include Incidence_Geometry
        type parallel = (l:Line, m: Line) 
            -> (P:Point) -> (|- !on(P,l) | !on(P,m)) 
    }

    //Definition 2.6.1. Two lines are said to intersect if there exists a point that lies on both lines.
    theory intersect{
        include Incidence_Geometry
        type intersect = (l: Line, m: Line)
            -> (P: Point, |- on(P,l) & on(P,m))
    }

    theory experiments{
        include Incidence_Geometry
        A: Point
        B: Point
        C: Point
        l: Line
        m: Line
        onAl: |- on(A,l)
        onAm: |- on(A,m)
        np: notParallel(l,m)
        hi: _ = np(1)
    }
    
}