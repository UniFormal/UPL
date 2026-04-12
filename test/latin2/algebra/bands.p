module bands {
    theory Band {
        include .magmas.Semigroup
        include .magmas.Idempotent
    }

// This follows the lattice structure graphic from:
// https://en.wikipedia.org/wiki/Band_(algebra)
//
// Each dashed line is a new row

// -----------------------------------------------

    theory Regular {
        include Band
        regular:--- z∘(x∘(z∘(y∘z))) == z∘(x∘(y∘z))
    }

// -----------------------------------------------

    theory LeftNormal {
        include Band
        left_normal:--- z∘(x∘(z∘y)) == z∘(x∘y)
    }

    theory RightNormal {
        include Band
        right_normal:--- y∘(z∘(x∘z)) == y∘(x∘z)
    }

// -----------------------------------------------

    theory LeftRegular {
        include Band
        left_regular:--- (x∘y)∘x == x∘y
    }

    theory Normal {
        include Band
        normal:--- z∘((x∘y)∘z) == z∘((y∘x)∘z)
    }

    theory RightRegular {
        include Band
        right_regular:--- y∘(x∘y) == x∘y
    }

// -----------------------------------------------

    theory RightAbelian {
        include Band
        right_abelian:--- z∘(x∘y) == z∘(y∘x)
    }

    theory Rectangular {
        include Band
        rectangular:--- x∘(y∘x) == x

        // provable
        rectangularAny:--- x∘(y∘z) == x∘z
    }

    theory LeftAbelian {
        include Band
        left_abelian:--- (x∘y)∘z == (y∘x)∘z
    }

// -----------------------------------------------
    
    theory LeftZero {
        include Band
        left_zero:--- x∘y == x
    }

    theory Semilattice {
        include Band
        include .magmas.Abelian
    }

    theory RightZero {
        include Band
        right_zero:--- x∘y == y
    }

// -----------------------------------------------

    theory Trivial {
        include Band
        trivial:--- x == y
    }

// -----------------------------------------------
}