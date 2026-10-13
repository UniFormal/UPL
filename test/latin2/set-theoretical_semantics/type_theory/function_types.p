module set_sem_function_types {
    theory SimpleFunctionTypesSet {
        include .set_sem_fundamentals.TypesSet
        include .set_relations.Functions
    }

    // I don't think I can do this
    theory DependentFunctionTypesSet {
        include .set_sem_fundamentals.TypedTermsSet
    }

    theory SimpleFunctionsSet {
        include .concepts.Propositions
        include .concepts.Proofs
        include SimpleFunctionTypesSet
        include .set_sem_fundamentals.TypedEqualityNDSet
        include .set_relations.LambdaFunction
    }
}
