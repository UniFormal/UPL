module bands {
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