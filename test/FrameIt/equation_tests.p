module equation_tests{
    type point
    f:point -> float = p -> 0.0
    g:point -> float = p -> 1.0
    gp: point

    theory T{
        p:point
        e: |- f(p) == 0
        s: (v:float, |- f(p) == v)

        // global point
        ge: |- f(gp) == 0
        gs: (v:float, |- f(gp) == v)
    }

    theory _Scroll{
        _A: point
        fixedValue : |- f(_A) == 0
        // How to write down the equalities if the value is unknown?
        // v1 just ???
        v1: |- f(_A) == ???
        // v2 have the value as its own declaration
        v: float
        v2: |- f(_A) == v
        // v3 Sigma-type
        v3: (v:float,|- f(_A) == v)
        __res: |- g(_A) == f(_A) + 1

        // global point
        gfixedValue : |- f(gp) == 0
        // v1 just ???
        gv1: |- f(gp) == ???
        // v2 have the value as its own declaration
        gv: float
        gv2: |- f(gp) == v
        // v3 Sigma-type
        gv3: (v:float,|- f(gp) == v)
        g__res: |- g(gp) == f(gp) + 1
    }

    theory equation_tests{
        include T
        include _Scroll
        _A = p
        p = _A

        fixedValue = e
        v1 = e
        v2 = e
        // access the value encoded in e.g. ground_dist?
        magic:_
        v = magic(e)
        v2 = e
        v3 = s
        
        // global point
        gfixedValue = ge
        gv1 = ge
        gv2 = ge
        // access the value encoded in e.g. ground_dist?
        gmagic:_
        gv = gmagic(ge)
        gv2 = ge
        gv3 = gs
    }
}