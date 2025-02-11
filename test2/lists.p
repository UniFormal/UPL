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

    test = quickSort([2,5,1,7,8]) == [1,2,5,7,8]
}