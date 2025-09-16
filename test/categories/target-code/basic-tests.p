module Tests {

    // test non-monadic components of the code
    els = []
    ls: list[int] = [1,2,3,4]
    ls2: [int] = [1,2,3,4]
    s: set[int] = ls
    s2: set[int] = [1,2,3,4]
    s3: set[int] = [1,2,3,3]
    s4: set[int] = [1,2,3]
    // int -> list[char] doesn't work
    maptochar: int -> [string] = n -> n match {
        1 -> ["a"]
        2 -> ["b"]
        3 -> ["c"]
        4 -> ["d"]
    }

    // evaluate to false
    //
    // s == s2
    // s2 == ls


    test = {
        1 == 1 &
        els == [] &
        ls == [1,2,3,4] &
        ls == ls2 &
        maptochar(1) == ["a"] &
        s == ls &
        s3 == s4 &
        s3 == set[1,2,3]

    }

}