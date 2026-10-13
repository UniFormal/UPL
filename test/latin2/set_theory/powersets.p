module powersets {
    theory Powersets {
        include .setbase.SetBase
    }

    theory PowersetsEmpty {
        include Powersets
        include .finite_sets.EmptySet
    }
}
