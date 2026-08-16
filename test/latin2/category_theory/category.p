module category {
    include .sfol.SFOLEQND

    theory Class {
        type obj
    }

    theory Category {
        include Class
        hom: obj -> obj -> tp
        type Hom(o1: obj, o2: obj) = (a,b) -> tm (hom a b)
        ident: a -> Hom (a a)
        comp: (a,b,c) -> Hom (a b) -> Hom (b c) -> Hom (a c)

        neutLeft: (a,b,f) -> ded tequal(Hom a b, comp(a,a,b) (ident a) f, f)
        neutRight: (a,b,f) -> ded tequal(Hom a b, comp(a,b,b) f (ident b), f)
        assoc: ???
        assoc_22_121: ???

        isos = ???
        iso = (a,b) -> ???

        iso_equiv: .relations.EquivalenceRelation {
            type carrier = obj
            type rel(c1, c2) = ded iso(c1, c2)
            refl = ???
            sym = ???
            trans = ???
        }
    }

    theory SmallClass {
        sobj: tp
        realize Class
        type obj = tm sobj
    }

    theory SmallCategory {
        include SmallClass
        include Category
    }
}