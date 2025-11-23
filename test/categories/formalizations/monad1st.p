module MonST {

    // make use of theory EndofunctorST from functorst.p
    //import test.categories.categoryst
    //import test.categories.functorst


    theory MonadST {
        // Derivation from functors
        // A monad is an endofunctor T with 2 operations (natural transformations) join and return that
        // satisfy four laws.

        // include EndofunctorST
        // T = EndofunctorST {}
        T: FunST.EndofunctorST
        I: FunST.IdentityFunctor {C = T.C}
        TT: FunST.FunctorComposition {F = T, G = T}
        // pure: NatTransST.NaturalTransformationST {F = I, G = T}
        // produces errors:
        // missing definition forC
        //   val C : .CatST.CategoryST = ..{F}{C}
        //   val C : .CatST.CategoryST while checking T
        // clashing definitions for D
        //   val D : .CatST.CategoryST = ..{F}{D}
        //   val D : .CatST.CategoryST = C while checking T
        //join: NatTransST.NaturalTransformationST {F = T, G = TT}

        // 1. condition: join . T join == join . join T     : T^3 -> T

        // 2. condition: join . T pure == join . pure T     : T -> T

    }
}