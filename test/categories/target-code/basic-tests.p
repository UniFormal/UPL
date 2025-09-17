module Tests {

    // test non-monadic components of the code

    // lists
    els = []
    ls: list[int] = [1,2,3,4]
    ls2: [int] = [1,2,3,4]

    // chars
    // c: char = 'a' // produces error
    //c: string = "a"

    // int -> list[char] doesn't work
    maptochar: int -> [string] = n -> n match {
        1 -> ["a"]
        2 -> ["b"]
        3 -> ["c"]
        4 -> ["d"]
    }


    // sets
    s: set[int] = ls
    s2: set[int] = [1,2,3,4]
    s3: set[int] = [1,2,3,3]
    s4: set[int] = [1,2,3]


    // tuples
    t: (int,string) = (1,"foo")
    t1: int = t(1)
    // unary tuple
    ut: (int) = (1) // not a tuple
    ut2: int = 1
    // ut3: (int,) = (1,) // produces error, not possible to define unary tuple
    // ternary tuple
    tt: (int, string, bool) = (1,"foo",true)


    // options produce errors
    // o1: Option[int] = Some(1)
    // o2: Option[int] = None
    o1: option[int] = [1]
    o11: option[int] = option[1]
    o2: option[int] = []

    // ranges
    range: (int,int) -> [int]
    range =  (m,n) -> {
        if (m==n) return [n]
        (m -: range(m+1,n))
    }
    rls = range(1,4)

    // arithmetic operators
    a = 1 + 2
    b = 4 - 1
    // type coercion problematic
    c: int = 3 * 1
    d = 9 / 3
    e = 3 ^ 2


    test = {
        lstest: bool = 1 == ls[0] &
            els == [] &
            ls == [1,2,3,4] &
            ls == ls2 &
            maptochar(1) == ["a"]

        val stest1 = s == ls &       // removing type declaration produces error
            s3 == s4 &
            s3 == set[1,2,3]

        stest2: bool = s == s2 | s2 == ls     // false, hard to explain

        ttest: bool = t == (1,"foo") & 1 == t1 & "foo" == t(2) & ut == ut2 & tt(3)

        // o3: option[int] = [1,2] // parses no more
        // o4: option[int] = option[1,2] // doesn't
        otest: bool = o1 == o11 & o1 != o2 & o1 == [1] & o2 == [] // & o1 == o4

        // type coercion doesn't work between options and singleton lists
        //o5: [int] = [1]
        //otest2: o1 == o5

        rtest: bool = ls == rls

        arithtest: bool = a == b & //c == d
            e == 9

        lstest & stest1 & ttest & otest & rtest & arithtest
    }

}