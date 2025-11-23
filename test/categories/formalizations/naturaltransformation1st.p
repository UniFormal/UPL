module NatTransST {

    theory NaturalTransformationST {
        // Given categories C,D and functors F,G from C to D, a natural transformations is a family of morphisms in D

        // Have two functors F and G, which must be defined on the same two categories
        F: FunST.FunctorST
        G: FunST.FunctorST {C = F.C, D = F.D}
        // problems of computability, term level definition in type declaration.

        // A natural transformation must associate for every object X in C a morphism alpha: F(X) -> G(X) in D
        alpha: F.C.object -> G.D.morphism
        // fromto_axiom: |- forall x: F.C.object. G.D.fromTo(alpha(x), F.Fo(x), G.Fo(x))

        // produces typechecking errors:
        // found: F{D}{object}; expected: G{D}{object} while checking F{Fo}(x)
        // found: F{C}{object}; expected: G{C}{object} while checking x
        // found: G{D}{object}; expected: G{D}{object} while checking G{Fo}(x)

        // commutative diagram: For every morphism f:X->Y in C we have  G(f) . alpha(X) == alpha(Y) . F(f)
        // the naturality square satisfies the naturality condition:    G(f) . alpha(a) == alpha(b) . F(f)
        // naturality_condition: |- forall a,b,f. F.C.fromTo(f,a,b) => G.D.compose(alpha(a),G.Fm(f)) == G.D.compose(F.Fm(f),alpha(b))

        // produces typechecking errors:
        // found: F{C}{morphism}; expected: G{C}{morphism} while checking f
        // found: F{D}{morphism}; expected: G{D}{morphism} while checking F{Fm}(f)
    }




}