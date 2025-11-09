module CollectionMonad {

    theory CollectionMonad {
        type X

        return: X -> collection[X] = (x: X) -> collection[x]
    }

    OptionMonad = CollectionMonad {
        type collection = option
    }

    intOptionMonad = OptionMonad {
        type X = int
    }
}