module ringoids {
    theory BiMagma {
        include .sets.Set
    }

    theory Ringoid {
        include BiMagma
    }

    theory CommRingoid {
        include Ringoid
    }

    theory MonoidalRingoid {
        include Ringoid
    }

    theory BiMonoid {
        include MonoidalRingoid
    }

    theory NonZeroInvertible {
        include BiMonoid
    }

    theory NoZeroDividers {
        include BiMonoid
    }

    theory NonTrivialRing {
        include BiMonoid
    }

    theory Semiring {
        include BiMonoid
    }

    theory CommSemiring {
        include Semiring
        include CommRingoid
    }

    theory NearRing {
        include BiMonoid
    }

    theory CommNearRing {
        include NearRing
        include CommRingoid
    }

    theory Ring {
        include NearRing
    }

    theory BooleanRing {
        include Ring
    }

    theory CommRing {
        include Ring
        include CommRingoid
    }

    theory IntegralDomain {
        include CommRing
        include NoZeroDividers
    }

    theory SkewField {
        include Ring
        include NonZeroInvertible
        include NonTrivialRing
    }

    theory Field {
        include SkewField
        include CommRingoid
    }

    theory BilinearRingoid {
        include Ringoid
    }

    theory LieRing {
        include Ring
        include BilinearRingoid
    }
}
