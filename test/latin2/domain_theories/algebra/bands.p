module bands {
    // regular bands and views between them
    // mostly following the wikipedia page on Bands
    //
    // Notes:
    // - some names that were not given on Wikipedia are made up
    // - most views do not actually use (all of) the Band properties
    // - LeftX and RightX are stronger than X, not weaker

    theory Regular {
        include .magmas.Band
    }

    theory LeftNormal {
        include .magmas.Band
    }

    theory LeftRegular {
        include .magmas.Band
    }

    theory RightNormal {
        include .magmas.Band
    }

    theory RightRegular {
        include .magmas.Band
    }

    // views for the three stages of regular band theories

    // Regular2LeftNormal: LeftNormal -> Regular = r -> §{
    //     include .magmas.Band
    // }

    // LeftNormal2LeftRegular: LeftRegular -> LeftNormal = l -> §{
    //     include .magmas.Band
    // }

    // Regular2RightNormal: RightNormal -> Regular = r -> §{
    //     include .magmas.Band
    // }

    // RightNormal2RightRegular: RightRegular -> RightNormal = r -> §{
    //     include .magmas.Band
    // }

    // normal bands

    theory Normal {
        include .magmas.Band
    }

    theory RightCommutative {
        include .magmas.Band
    }

    theory LeftCommutative {
        include .magmas.Band
    }

    // views for the diamond of normal band theories (with semilattices at the bottom)

    // Normal2RightCommutative: RightCommutative -> Normal = n -> §{
    //     include .magmas.Band
    // }

    // Normal2LeftCommutative: LeftCommutative -> Normal = n -> §{
    //     include .magmas.Band
    // }

    // RightCommutative2Semilattice: .magmas.Semilattice -> RightCommutative = r -> §{
    //     include .magmas.Band
    // }

    // LeftCommutative2Semilattice: .magmas.Semilattice -> LeftCommutative = l -> §{
    //     include .magmas.Band
    // }

    // views from regular to normal band theories

    // LeftNormal2Normal: Normal -> LeftNormal = l -> §{
    //     include .magmas.Band
    // }

    // LeftRegular2RightCommutative: RightCommutative -> LeftRegular = l -> §{
    //     include .magmas.Band
    // }

    // RightNormal2Normal: Normal -> RightNormal = r -> §{
    //     include .magmas.Band
    // }

    // RightRegular2LeftCommutative: LeftCommutative -> RightRegular = r -> §{
    //     include .magmas.Band
    // }

    // rectangular bands (the axioms here already imply idempotency)

    theory Rectangular {
        include .magmas.Band
    }

    theory LeftZero {
        include .magmas.Band
    }

    theory RightZero {
        include .magmas.Band
    }
}
