module Tests {

    theory ListApp {
        type X
        append: (list[X], list[X]) -> list[X]
        append = (xs, ys) -> {
            xs match {
                [] -> ys
                x -: xs2 -> x -: append(xs2, ys)
            }
        }
    }

    intListApp = ListApp {
        type X = int
    }

    theory TypeVar {
        type X
        type Y = option[X]
    }

    intTypeVar = TypeVar {
        type X = int
        y: Y = [1]
    }

    theory HkTypeVar {
        type A
        //type M[A]
    }

    test = {
        true &
        intListApp.append([1,2], [3,4]) == [1,2,3,4] &
        intTypeVar.y == [1]
    }
}