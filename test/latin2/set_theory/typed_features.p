module typed_features {
    // This file was mainly from LATIN, but MMT can do this differently. Therefore this shall be ignored

    theory TBigUnion {
        include .typebase.TypeBase
    }

    theory TBigIntersection {
        include .typebase.TypeBase
        include .setbase.EmptyDefinitions
    }

    theory TImage {
        include .typebase.TypeBase
    }

    theory TPowersets {
        include .typebase.TypeBase
        include .powersets.Powersets
        include .operations.Filter
        include .setbase.SubsetExtensionality
    }
}
