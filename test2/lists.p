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


    depth_first_search = (l:int) -> (k:int) -> (m:[(int,int)]) -> {
        var stack = get(l)(m)
        var ans = false
        var break = true
        while (break){
            stack match {
                x -: y -> {
                    if(x == k) {ans = true
                    break = false}else{
                        val temp = get(x)(m)
                        stack = temp + stack
                    }
                    }
            }
        }
        ans
    }
    test = depth_first_search(1)(4)([(1,2),(1,3),(2,4),(2,5),(3,6),(3,7)])
}