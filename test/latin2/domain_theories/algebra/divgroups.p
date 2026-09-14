module divgroups {
    theory DivGroup {
        include .sets.Set
    }

    // GroupToDivGroup: DivGroup -> .groups.Group = g -> §{
    //     include .sets.Set
    // }

    // DivGroupToGroup: .groups.Group -> DivGroup = d -> §{
    //     include .sets.Set
    // }

    theory GroupToGroup_Eq {
        include .groups.Group
    }

    theory DivGroupToDivGroup_Eq {
        include DivGroup
    }
}
