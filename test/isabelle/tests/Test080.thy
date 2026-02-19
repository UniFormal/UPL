theory Test080
  imports Complex_Main
begin

definition a :: "int" where
  "a = (1 + 2 + 3)"
definition b :: "int" where
  "b = (1 - 2 - 3)"
definition c :: "int" where
  "c = (1 * 2 * 3)"
definition d :: "rat" where
  "d = (1 / 2 / 3)"
definition f :: "int" where
  "f = ((1 + 2) - 3)"
definition g :: "int" where
  "g = (1 + (2 * 3))"
definition h :: "rat" where
  "h = ((1 * 2) / 3)"
definition i :: "real" where
  "i = ((1 / 2) - 3.0)"
definition j :: "complex" where
  "j = ((1 ^ 2) + 3 + 4 + 5 + 6)"
definition k :: "complex" where
  "k = ((1 + 2 + (3 ^ 4) + 5) - 6)"
definition l :: "complex" where
  "l = ((1 ^ 2) + (3 ^ 4) + (5 ^ 6))"
definition m :: "complex" where
  "m = (1 * (2 ^ 3) * ((4 ^ 5) / 6))"
definition n :: "real" where
  "n = (1.100000023841858 + 2.200000047683716 + 3.299999952316284)"
definition oo :: "real" where
  "oo = ((1.100000023841858 - 2.200000047683716) + 3.299999952316284)"
definition p :: "real" where
  "p = (1.100000023841858 + (2.200000047683716 * 3.299999952316284))"
definition q :: "real" where
  "q = (1.100000023841858 * 2.200000047683716 * 3.299999952316284 * 4.400000095367432 * 5.0)"
definition x :: "int" where
  "x = (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9)"

end