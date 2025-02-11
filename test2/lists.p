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
    test = (append2([1,2,3])([4,5,6]) == [3,2,1,4,5,6])
}