module axioms {
    theory PairingAx {
        include .setbase.SetBase
    }

    theory UnionAx {
        include .setbase.SetBase
    }

    theory PowersetAx {
        include .setbase.SetBase
    }

    theory ComprehensionAx {
        include .setbase.SetBase
    }

    theory ReplacementAx {
        include .setbase.SetBase
        include .setbase.RelationDefinitions
    }

    theory RegularityAx {
        include .setbase.SetBase
    }

    // These are special cases of regularity. Maybe it should be moved to a file
    // containing features, but for now there is no suitable file
    theory Acyclic {
        include .setbase.SetBase
    }

    theory InfinityAx {
        // There exists an successor set A containing empty and for every element x of A, the successor
        // of x is a member of A as well.
        include .finite_sets.EmptySet
    }

    theory ChoiceAx {
        include .setbase.SetBase
        include .setbase.EmptyDefinitions
        include .setbase.DisjointDefinitions
    }
}
