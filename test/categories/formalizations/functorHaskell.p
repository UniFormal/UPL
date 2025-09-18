module FunHask {

    theory Type {
       type univ
    }

    theory TypeConstructor {
        // a type constructor is a function from zero or more types to a type
        // examples in Haskell are:
        //      Maybe (a -> Maybe a)
        //      List constructor [] (a -> [a])
        //      Tuple type constructor (,): binary (a -> b -> (a,b)), ternary (a -> b -> c -> (a,b,c))

        // want a notion of type constructors that take arbitrarily many arguments
        // compare with varargs (variable number of arguments) in scala *
        //typeConstructor: Type* -> Type

        // for functors unary type constructors (exactly one type parameter) are sufficient
        typeConstructorUnary: Type -> Type
    }

    theory FunctorHaskell {
        // functors in Haskell are defined on unary type constructors with a single type parameter
        // example of a unary polymorphic type: Maybe a
        functorTypeConstructor = TypeConstructor.typeConstructorUnary

        // the type constructor represents the object mapping in the category Hask of Haskell types
        // that a functor in Haskell is an endofunctor in the category of Hask is only implicit in this representation
        // Actually it is the category of UPL types Type
        a: type
        b: type

        // the fmap represents the morphism mapping of the functor
        fmap: (a -> b) -> functorTypeConstructor(a) -> functorTypeConstructor(b)

        // functor laws
        id_1: a -> a = (x:a) -> x
        id_2: functorTypeConstructor(a) -> functorTypeConstructor(a) = (x:functorTypeConstructor(a)) -> x

        // 1. law: preservation of identity
        id_law: |- forall x: functorTypeConstructor(a). fmap(id_1)(x) == id_2(x)

        // 2. law: preservation of composition
        c: type
        f: a -> b
        g: b -> c
        comp_law: |- forall x: functorTypeConstructor(a).
                            fmap((y:functorTypeConstructor(a)) -> g(f(y)))(x) == fmap(g)(fmap(f)(x))

    }

    theory MaybeFunctor {
        include functorHaskell
        functorTypeConstructor = Option

        fmap = (f: a -> b) -> (x: Option[a]) -> {
            x match {
                None -> None
                Some(y) -> Some(f(y))
            }
        }

        // can already prove laws without instantiating a, b
        // id_law = ???
        // comp_law = ???
    }
}