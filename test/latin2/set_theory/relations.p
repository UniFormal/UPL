module set_relations {
    theory TheRelation {
        include .setbase.SetBase
        include .setbase.RelationDefinitions
    }

    theory Relations {
        include TheRelation
    }

    theory PartialFunctions {
        include TheRelation
    }

    theory Functions {
        include TheRelation
    }

    // Lambda shall later be used to formalize function_types. However, the definition of
    // lambda s.t. it is usable for function_types is harder than expected
    theory LambdaFunction {
        include TheRelation
    }

    theory LambdaImage {
        include LambdaFunction
        include .operations.Image
    }
}
