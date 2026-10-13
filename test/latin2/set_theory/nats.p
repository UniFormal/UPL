module nats {
    theory NatNums {
        include .views_operations.UnionSingleton
        include .views_lattice_operations.BigIntersectionUnorderedPairs
        include .lattice_operations.Intersection
        include .operations.Adjoin
        include .zfc.ZFFeatures
        include .setbase.SubsetExtensionality
        include .lattice_operations.UnionEmpty
    }

    theory Nats {
        include NatNums
    }
}
