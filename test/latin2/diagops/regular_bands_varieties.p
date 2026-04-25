module regular_bands_varieties {
    theory Carrier {
        type univ
    }

    theory Magma {
        include Carrier
        op: (univ,univ) -> univ # infix ∘
    }

    theory Commutative {
        include Magma
        comm:--- x∘y == y∘x
    }

    theory Idempotent {
        include Magma
        idem:--- x∘x == x
    }

    theory Semigroup {
        include Magma
        assoc:--- x∘(y∘z) == (x∘y)∘z
    }

    theory Band {
        include Idempotent
        include Semigroup
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Regular Band: the top of the lattice
    // Axiom: zxyz = zxzyz
    // ─────────────────────────────────────────────────────────────────────────
    theory RegularBand {
        include Band
        regular:--- (((z∘x)∘y)∘z) == ((((z∘x)∘z)∘y)∘z)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Level 2 (just below RegularBand): two incomparable varieties
    //
    //   LeftNormal:  zxy = zxzy
    //   RightNormal: yxz = yzxz
    // ─────────────────────────────────────────────────────────────────────────

    // Left-normal band: zxy = zxzy
    theory LeftNormalBand {
        include Band
        leftNormal:--- ((z∘x)∘y) == (((z∘x)∘z)∘y)
    }

    // Right-normal band: yxz = yzxz
    theory RightNormalBand {
        include Band
        rightNormal:--- ((y∘x)∘z) == (((y∘z)∘x)∘z)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Level 3: three incomparable varieties
    //
    //   LeftRegular:  xy = xyx
    //   Normal:       zxyz = zyxz
    //   RightRegular: xy = yxy
    // ─────────────────────────────────────────────────────────────────────────

    // Left-regular band: xy = xyx
    theory LeftRegularBand {
        include Band
        leftRegular:--- (x∘y) == ((x∘y)∘x)
    }

    // Normal band: zxyz = zyxz
    theory NormalBand {
        include Band
        normal:--- (((z∘x)∘y)∘z) == (((z∘y)∘x)∘z)
    }

    // Right-regular band: xy = yxy
    theory RightRegularBand {
        include Band
        rightRegular:--- (x∘y) == ((y∘x)∘y)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Level 4: three incomparable varieties
    //
    //   RightCommutativeBand: zxy = zyx  (x,y commute on the right of z)
    //   RectangularBand:      xyx = x
    //   LeftCommutativeBand:  xyz = yxz  (x,y commute on the left of z)
    // ─────────────────────────────────────────────────────────────────────────

    // Left-semimedial band: zxy = zyx  (commutativity on the right side)
    theory RightCommutativeBand {
        include Band
        rightComm:--- ((z∘x)∘y) == ((z∘y)∘x)
    }

    // Rectangular band: xyx = x
    theory RectangularBand {
        include Band
        rectangular:--- ((x∘y)∘x) == x
    }

    // Right-semimedial band: xyz = yxz  (commutativity on the left side)
    theory LeftCommutativeBand {
        include Band
        leftComm:--- ((x∘y)∘z) == ((y∘x)∘z)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Level 5: three incomparable varieties (atoms above the trivial variety)
    //
    //   LeftZeroBand:  xy = x
    //   Semilattice:   xy = yx
    //   RightZeroBand: xy = y
    // ─────────────────────────────────────────────────────────────────────────

    // Left-zero band: xy = x
    theory LeftZeroBand {
        include Band
        leftZero:--- (x∘y) == x
    }

    // Semilattice: commutative band (xy = yx)
    theory Semilattice {
        include Band
        include Commutative
    }

    // Right-zero band: xy = y
    theory RightZeroBand {
        include Band
        rightZero:--- (x∘y) == y
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Bottom: trivial variety
    //
    //   Trivial: x = y  (all elements are equal)
    // ─────────────────────────────────────────────────────────────────────────

    theory TrivialBand {
        include Band
        trivial:--- x == y
    }
}
