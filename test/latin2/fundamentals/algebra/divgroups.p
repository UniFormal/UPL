module meta_divgroups {
    theory DivGroup {
        include .relations.EqualityType
        e : carrier
        div: (carrier, carrier) -> carrier
        self_div:--- div(x, x) == e
        unit_neutR:--- div(x, e) == x
        reciprocal:--- div(e, div(x, y)) == div(y, x) 
        reduce:--- div(div(x, z), div(y, z)) == div(x, y)
    }

    // GroupToDivGroup: DivGroup -> .groups.Group = g -> §{
    //     include .relations.EqualityType
    // }

    // DivGroupToGroup: .groups.Group -> DivGroup = d -> §{
    //     include .relations.EqualityType
    // }

    theory GroupToGroup_Eq {
        include .groups.Group
    }

    theory DivGroupToDivGroup_Eq {
        include DivGroup
    }
}