module views_relations {
    // The views currently still need single theories as a domain and codomain, which
    // forces us to provide spurious named theories. This should be refactored when
    // multi-theory domains and codomains are possible.

    // Views for TheRelation
    theory CartFilter {
        include .cartesian_product.CartesianProduct
        include .operations.Filter
        include .setbase.RelationDefinitions
    }

    // TheCartFilter: CartFilter -> .set_relations.TheRelation = t -> §{
    //     include .setbase.SetBase
    //     include .setbase.RelationDefinitions
    // }

    // Views for Relations
    theory CartFilterPower {
        include CartFilter
        include .powersets.Powersets
    }

    // RelCartFilter: CartFilterPower -> .set_relations.Relations = r -> §{
    //     include .set_relations.TheRelation
    // }

    // Views for PartialFunctions
    theory RelFilter {
        include .set_relations.Relations
        include .operations.Filter
    }

    // PFuncRelFilter: RelFilter -> .set_relations.PartialFunctions = p -> §{
    //     include .set_relations.TheRelation
    // }

    // PFuncCartFilter: CartFilterPower -> .set_relations.PartialFunctions = p -> §{
    //     include .set_relations.TheRelation
    // }

    // // Views for Functions
    // FuncRelFilter: RelFilter -> .set_relations.Functions = f -> §{
    //     include .set_relations.TheRelation
    // }

    theory PFuncFilter {
        include .set_relations.PartialFunctions
        include .operations.Filter
    }

    // FuncPFuncFilter: PFuncFilter -> .set_relations.Functions = f -> §{
    //     include .set_relations.TheRelation
    // }

    // FuncCartFilter: CartFilterPower -> .set_relations.Functions = f -> §{
    //     include .set_relations.TheRelation
    // }

    // Views for LambdaFunction
    theory TheBigCartFilterImage {
        include CartFilter
        include .lattice_operations.BigUnion
        include .operations.Image
        include .cartesian_product.Img
    }

    // LambdaCartFilter: TheBigCartFilterImage -> .set_relations.LambdaFunction = l -> §{
    //     include .set_relations.TheRelation
    // }

    theory BigLambda {
        include TheBigCartFilterImage
        include .set_relations.LambdaFunction
    }

    // TheLambda: BigLambda -> .set_relations.LambdaImage = t -> §{
    //     include .set_relations.LambdaFunction
    //     include .operations.Image
    // }
}
