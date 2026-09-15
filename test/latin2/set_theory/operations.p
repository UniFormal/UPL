module operations {
    theory Filter {
        include .setbase.SetBase
    }

    theory Replace {
        include .setbase.SetBase
        include .setbase.RelationDefinitions
    }

    theory Image {
        include .setbase.SetBase
    }

    theory ImageEmpty {
        include Image
        include .finite_sets.EmptySet
    }

    theory SymmetricDifference {
        include .setbase.SetBase
    }

    theory SymmetricDifferenceEmpty {
        include SymmetricDifference
        include .finite_sets.EmptySet
    }

    theory Adjoin {
        include .setbase.SetBase
    }

    theory Remove {
        include .setbase.SetBase
    }
}
