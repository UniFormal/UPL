module set_sem_product_types {
    theory SimpleProductTypesSet {
        include .set_sem_fundamentals.TypesSet
        include .cartesian_product.CartesianProduct
    }

    theory DependentProductTypesSet {
        include .set_sem_fundamentals.TypedTermsSet
        include .cartesian_product.SigmaMod
    }

    theory SoftDependentProductTypesSet {
        include .concepts.Propositions
        include .concepts.Terms
        include .set_sem_fundamentals.SoftTypedTermsSet
        include .cartesian_product.Sigma
    }

    theory SimpleProductsSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .set_sem_fundamentals.TypedEqualitySet
        include SimpleProductTypesSet
    }

    theory DependentProductsSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include DependentProductTypesSet
        include .set_sem_fundamentals.TypedEqualitySet
        include .set_sem_fundamentals.DependentTypeEqualitySet
    }

    theory SoftTypedProductsSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .concepts.Terms
        include .equality.UntypedEquality
        include .cartesian_product.CartesianProduct
    }

    theory SoftTypedSimpleProductsSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .concepts.Terms
        include .equality.UntypedEquality
        include .set_sem_fundamentals.SoftTypedTermsSet
        include SoftTypedProductsSet
        include SimpleProductTypesSet
    }

    theory SoftTypedDependentProductsSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .concepts.Terms
        include .equality.UntypedEquality
        include .set_sem_fundamentals.SoftTypedTermsSet
        include SoftTypedProductsSet
        include SoftDependentProductTypesSet
    }

    theory SimpleProductsExpandSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include SimpleProductsSet
    }

    theory DependentProductsExpandSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include DependentProductsSet
    }

    theory SoftTypedProductsExpandSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .concepts.Terms
        include .equality.UntypedEquality
        include SoftTypedProductsSet
    }

    theory SimpleProductsExtensionalitySet {
        include .concepts.Propositions
        include .concepts.Proofs
        include SimpleProductsSet
    }

    theory DependentProductsExtensionalitySet {
        include .concepts.Propositions
        include .concepts.Proofs
        include DependentProductsSet
    }

    theory SoftTypedProductsExtensionalitySet {
        include .concepts.Propositions
        include .concepts.Proofs
        include .concepts.Terms
        include .equality.UntypedEquality
        include SoftTypedProductsSet
    }
}
