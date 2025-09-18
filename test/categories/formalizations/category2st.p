module Cat3 {

    // alternative formalization that uses only morphisms and no objects
    theory Category3 {
        // identity morphisms can represent objects
        type morphism

        // some morphisms are identity morphisms
        // And identity morphisms can represent objects
        id_pred: morphism -> bool

        // So in principle from category1st to category2st:
        // we only need to define an additional predicate and change the type object to morphism

        domain: morphism -> morphism
        codomain: morphism -> morphism

        fromTo = (f,a,b) -> domain(f) == a & codomain(f) == b
        composable = (f,g) -> codomain(f) == domain(g)

        id: morphism -> morphism
        id_fromto: |- forall a. fromTo(id(a),a,a)

        // this must be a partial function, compose(f,g) is defined only if composable(f,g)
        compose: (morphism,morphism) -> morphism
        compose_fromto: |- forall f,g. composable(f,g) => fromTo(compose(f,g), domain(f), codomain(g))

        // optionally: we make composition formally a total function by assigning an arbitrary result
        // alternatively, without this axiom, the composition of non-composable morphisms is simply unspecified
        compose_total: |- forall f,g. !composable(f,g) => compose(f,g) == f

        neutLeft:  |- forall a,f. domain(f) == a => compose(id(a), f) == f
        neutRight: |- forall a,f. codomain(f) == a => compose(f,id(a)) == f
        // may omit composable(g,h), because compose(compose(f,g), h) == compose(f,g) == compose(f, compose(g,h))
        assoc: |- forall f,g,h. composable(f,g) & composable(g,h) => compose(compose(f,g), h) == compose(f, compose(g,h))
    }

}