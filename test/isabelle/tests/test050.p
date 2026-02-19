module Test050 {

    // test all operators

    a = true & false
    b = true | false
    c = !false
    d = false => true
    e = 1 + 2
    f = 1 - 2
    g = 21 * 2
    h = 21 / 2
    i = 10 min -10
    j = 10 max -10
    k = 2^3
    l = -(-(-10))
    m = 1 < 2
    n = 1 <= 2
    oo = 1 > 2
    p = 1 >= 2
    q: list[int] = [1,2,3,4,5]
    r = q ::: q
    s = 1 in set[1,2,3,4,5]
    t = 0 -: q
    u = q :- 6
    v = 0 == 1
    w = 0 != 1

}