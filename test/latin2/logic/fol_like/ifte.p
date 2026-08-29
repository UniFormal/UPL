module ifte {
    theory IfThenElse {
        include .equality.TypedEquality
        include .pl.Classical
        ifte: (A) -> prop -> tm A -> tm A -> tm A
        ifte_true: (A,c,x,y) -> ded c -> ded tequal(A, ifte A c x y, x)
        ifte_true: (A,c,x,y) -> (ded c -> inconsistent) -> ded tequal(A, ifte A c x y, y)
    }
}