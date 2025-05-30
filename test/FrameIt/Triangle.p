module Triangle{  

    map: (int -> int) -> option[int] -> option[int] 
     = (f: rat -> rat) -> l -> l match{
        [] -> []
        [x] -> [f(x)]
    }

    type num = rat

    theory LineSegment{
        from: point
        to: point
        length: num
    }

    theory Triangle{
        // The theory of Triangles is the theory of the three-point geometry
        type point
        type side = (point, point)
        //on: (point, side) -> bool

        A : point
        B : point
        C : point

        a : side = (A,B)
        b : side
        c : side
    }


    a: Side{from=B, to=C}
    b: Side{from=C, to=A}
    c: Side{from=A, to=B}

    // The angles
    alpha: num
    beta: num
    gamma: num

    
}