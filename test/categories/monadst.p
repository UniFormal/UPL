module MonST {

    // make use of theory EndofunctorST from functorst.p
    import test.categories.categoryst
    import test.categories.functorst

    theory MonadST {
        // A monad is an endofunctor T with 2 operations (natural transformations) join and return that
        // satisfy three laws.

        include EndofunctorST
        // T = EndofunctorST {}
        type monad
        T: monad

        // join :: T (T a) -> T a
        // mu :: T^2 -> T
        join: (monad,monad) -> monad

        // return :: a -> T a
        // nu :: Id -> T (IdentityFunctor -> MonadEndofunctor)
        return: () -> monad

        // also need identity natural transformation
        // identity :: T a -> T a
        // Id :: T -> T
        identity: monad -> monad

        // satisfies three identities
        // 1. mu . (mu . Id) == mu . (Id . mu)
        // Id is IdentityNaturalTransformation
        identity1: |- join(join(identity(T^3))) == T == join(identity(join(T^3)))

        // 2. Id . T == T == mu . (nu . T)

        // 3. T . Id == T == mu . (T . nu)

    }
}