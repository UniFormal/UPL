module Lists{
    append2 : _
    append2 = (l:[int]) -> (m:[int]) -> 
    l match {
            [] -> m
            x -: y -> {
                var z = (x -:m)
                append2(y)(z)
            }
        }
    append : _
    append = (l:[int]) -> (m:[int]) -> {
        m match {
            [] -> l
            x -: y -> append(l:-x)(y)
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
        var ans:[int] = [l]
        var break = true
        while (break){
            stack match {
                x -: y -> {
                    ans = ans + [x]
                    if(x == k) {
                    break = false}else{
                        val temp = get(x)(m)
                        stack = temp + stack
                    }
                    }
            }
        }
        ans
    }

    test = append([1,2,3,4])([5,6,7,8]) == [1,2,3,4,5,6,7,8]
}