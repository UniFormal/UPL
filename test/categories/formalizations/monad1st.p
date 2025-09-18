module MonST {

    // make use of theory EndofunctorST from functorst.p
    import test.categories.categoryst
    import test.categories.functorst

    theory MonadST {
        // Derivation from functors
        // A monad is an endofunctor T with 2 operations (natural transformations) join and return that
        // satisfy four laws.

        include EndofunctorST
        // T = EndofunctorST {}
        type monad
        T: monad

        // join :: T (T a) -> T a
        // mu :: T^2 -> T
        join: (monad,monad) -> monad

        // return :: a -> T a
        // nu :: Id -> T (IdentityFunctor -> MonadEndofunctor)
        unit: () -> monad

        // f: a -> b
        identity-unit: |- unit(f(x)) == map(f,unit(x))

        // satisfies three identities
        // 1. mu . (mu . Id) == mu . (Id . mu)
        // Id is IdentityNaturalTransformation
        identity1: |- join(fmap(join,mmma) == join(join(mmma) == ma

        // 2. Id . T == T == mu . (nu . T)
        identity2: |- join(map(unit,ma) == join(unit(ma)) == ma

        // 3. T . Id == T == mu . (T . nu)
        identity3: |- join(map(x -> map(f,x), mma)) == map(f, join(mma)) == mb

    }
}