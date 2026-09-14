module rel_orders {
    theory Order {
        include .rel_basics.Preorder
        include .rel_basics.AntiSymmetry
    }

    theory Infimum {
        include .rel_basics.Relation
    }

    theory Supremum {
        include .rel_basics.Relation
    }

    // OppositeRelation: .rel_basics.Relation -> .rel_basics.Relation = r -> §{
    //     include .sets.Set
    // }

    // OppositeInf: Supremum -> Infimum = i -> §{
    //     include OppositeRelation
    // }

    // OppositeSup: Infimum -> Supremum = s -> §{
    //     include OppositeRelation
    // }

    theory TopElement {
        include .rel_basics.Relation
    }

    theory BottomElement {
        include .rel_basics.Relation
    }

    // OppositeTop: BottomElement -> TopElement = t -> §{
    //     include OppositeRelation
    // }

    // OppositeBottom: TopElement -> BottomElement = b -> §{
    //     include OppositeRelation
    // }
}
