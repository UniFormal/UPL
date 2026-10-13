module meta_bands {
    theory Regular {
        include .magmas.Band
        regular:--- z∘(x∘(z∘(y∘z))) == z∘(x∘(y∘z))
    }

    theory LeftNormal {
        include .magmas.Band
        left_normal:--- z∘(x∘(z∘y)) == z∘(x∘y)
    }

    theory RightNormal {
        include .magmas.Band
        right_normal:--- y∘(z∘(x∘z)) == y∘(x∘z)
    }

    theory LeftRegular {
        include .magmas.Band
        left_regular:--- (x∘y)∘x == x∘y
    }

    theory RightRegular {
        include .magmas.Band
        right_regular:--- y∘(x∘y) == x∘y
    }

    // views for the three stages of regular band theories

    Regular2LeftNormal: LeftNormal -> Regular = r -> §{
        include .magmas.Band
    }

    LeftNormal2LeftRegular: LeftRegular -> LeftNormal = l -> §{
        include .magmas.Band
    }

    Regular2RightNormal: RightNormal -> Regular = r -> §{
        include .magmas.Band
    }

    RightNormal2RightRegular: RightRegular -> RightNormal = r -> §{
        include .magmas.Band
    }

    theory Normal {
        include .magmas.Band
        normal:--- z∘((x∘y)∘z) == z∘((y∘x)∘z)
    }

    theory LeftCommutative {
        include .magmas.Band
        left_abelian:--- (x∘y)∘z == (y∘x)∘z
    }

    theory RightCommutative {
        include .magmas.Band
        right_abelian:--- z∘(x∘y) == z∘(y∘x)
    }

    // views for the diamond of normal band theories (with semilattices at the bottom)

    Normal2RightCommutative: RightCommutative -> Normal = n -> §{
        include .magmas.Band
    }

    Normal2LeftCommutative: LeftCommutative -> Normal = n -> §{
        include .magmas.Band
    }

    RightCommutative2Semilattice: .magmas.Semilattice -> RightCommutative = r -> §{
        include .magmas.Band
    }

    LeftCommutative2Semilattice: .magmas.Semilattice -> LeftCommutative = l -> §{
        include .magmas.Band
    }

    // views from regular to normal band theories

    LeftNormal2Normal: Normal -> LeftNormal = l -> §{
        include .magmas.Band
    }

    LeftRegular2RightCommutative: RightCommutative -> LeftRegular = l -> §{
        include .magmas.Band
    }

    RightNormal2Normal: Normal -> RightNormal = r -> §{
        include .magmas.Band
    }

    RightRegular2LeftCommutative: LeftCommutative -> RightRegular = r -> §{
        include .magmas.Band
    }

    theory Rectangular {
        include .magmas.Band
        rectangular:--- x∘(y∘x) == x

        // derivable
        rectangularAny:--- x∘(y∘z) == x∘z
    }
    
    theory LeftZero {
        include .magmas.Band
        left_zero:--- x∘y == x
    }

    theory RightZero {
        include .magmas.Band
        right_zero:--- x∘y == y
    }

    theory TrivialBand {
        include .magmas.Band
        trivial:--- x == y
    }
}