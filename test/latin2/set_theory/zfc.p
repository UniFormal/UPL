module zfc {
    // Some definitions are commented because they slow down type-checking.

    // ZFBase now contains all standard axioms of ZF instead of just Extensionality
    // and Existence.
    theory ZFBase {
        include .setbase.SetBase
        include .axioms.PairingAx
        include .axioms.UnionAx
        include .axioms.PowersetAx
        include .axioms.ComprehensionAx
        include .axioms.ReplacementAx
        include .axioms.RegularityAx
        // InfinityAx relies on Empty Set and should be added after defining Empty Set
    }

    theory ZF {
        include ZFBase
        include .finite_sets.UnorderedPairs
        include .lattice_operations.BigUnion
        include .powersets.Powersets
        include .operations.Filter
        include .operations.Replace
        // Acyclic is a special case of RegularityAx
        include .axioms.Acyclic
        // Empty is necessary for InfinityAx.
        include .finite_sets.EmptySet
        include .axioms.InfinityAx
    }

    // ZF and features that can be built from ZF
    theory ZFFeatures {
        include ZF
        include .lattice_operations.Union
        include .lattice_operations.BigIntersection
        include .lattice_operations.Intersection
        include .lattice_operations.Difference
        include .lattice_operations.Complement
        include .operations.SymmetricDifference
        include .finite_sets.Singletons
        include .operations.Adjoin
        include .operations.Remove
        include .operations.Image
        include .cartesian_product.CartesianProduct
        include .cartesian_product.Sigma
        include .set_relations.TheRelation
        include .set_relations.Relations
        include .set_relations.PartialFunctions
        include .set_relations.Functions
        include .set_relations.LambdaFunction
    }

    theory ZFC {
        include ZF
        include .axioms.ChoiceAx
    }

    theory ZFCFeatures {
        include ZFC
        include ZFFeatures
    }

    // typed versions of ZFC
    theory TypedZF {
        include .typebase.TypeBase
        include ZF
    }

    theory TypedZFFeatures {
        include TypedZF
        include ZFFeatures
    }
}
