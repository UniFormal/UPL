module Cat {

    theory Type {
       type univ
    }

    theory Category {
        // A category consists of objects and morphisms (arrows) between them.
        type object
        // This would be something "type morphism(object,object)" if UPL supported dependent base types
        morphism: (object, object) -> Type

        id: (a:object) -> morphism(a,a)
        op: (a,b,c, f: morphism(a,b), g:morphism(b,c)) -> morphism(a,c)

        neutLeft:  |- forall a,b, f: morphism(a,b). op(a,a,b,id(a), f) == f
        neutRight: |- forall a,b, f: morphism(a,b). op(a,b,b,f,id(b)) == f
        assoc: |- forall a,b,c,d, f: morphism(a,b), g: morphism(b,c), h: morphism(c,d). op(a,b,d,f,op(b,c,d,g,h)) == op(a,c,d,op(a,b,c,f,g), h)
    }

    // alternative formalization that uses only simple types
    theory CategoryST {
        type object
        type morphism
        domain: morphism -> object
        codomain: morphism -> object

        fromTo = (f,a,b) -> domain(f) == a & codomain(f) == b
        composable = (f,g) -> codomain(f) == domain(g)

        id: object -> morphism
        id_fromto: |- forall a. fromTo(id(a),a,a)

        // this must be a partial function, compose(f,g) is defined only if composable(f,g)
        compose: (moprhism,morphism) -> morphism
        compose_fromto: |- forall f,g. composable(f,g) => fromTo(compose(f,g), domain(f), codomain(g))

        // optionally: we make composition formally a total function by assigning an arbitrary result
        // alternatively, wihtout this axiom, the composition of non-composable morphisms is simply unspecified
        compose_total: |- forall f,g. !composable(f,g) => compose(f,g) == f

        neutLeft:  |- forall a,f. domain(f) == a => compose(id(a), f) == f
        neutRight: |- forall a,f. codomain(f) == a => compose(f,id(a)) == f
        assoc: |- forall f,g,h. composable(f,g) & composable(g,h) => compose(compose(f,g), h) == compose(f, compose(g,h))
    }

    unitCat = Category {
        type object = ()
        morphism = (a,b) -> Type {univ = ()}
        identity = a -> ()
        op = (a,b,c,f,g) -> ()

        neutLeft = ???
        neutRight = ???
        assoc = ???
    }

    test = {
        unitCat.op((),(),(),(),()) == ()
    }

}