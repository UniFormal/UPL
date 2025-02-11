module Lists{
    append2:_
    append2 = (l:[int]) -> (m:[int]) -> 
    l match {
            [] -> m
            x -: y -> {
                var z = (x -:m)
                append2(y)(z)
            }
        }
    
    quickSort : _
    quickSort = (l:[int]) -> l match {
        [] -> []
        x -: y -> {
            var smaller:[int] = []
            var larger : [int] = []
            for (i in y){
                if (i < x) {smaller = smaller + [i]} else {larger = larger + [i]}
                smaller = quickSort(smaller)
                larger = quickSort(larger)
            }
            smaller+[x]+larger
        }
    }
    length = (l:[int]) -> {
        var count = 0;
        for (_ in l){
            count = count + 1
        }
        count
    }

    get : int -> [(int,int)] -> [int] = l -> m -> {
        var x:[int] = []
        for (k in m){
            k match {
                (j,ans) -> if (j == l) {x = (x :- ans)}
            }
        }
        x
    }
    test = get(1)([(1,2),(1,3),(2,3)]) == [2,3]
}