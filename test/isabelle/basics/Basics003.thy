theory Basics003
  imports Main
begin

definition f1 :: "int => int" where
  "f1 = (\<lambda>x. (x + 1))"
definition f2 :: "int => int" where
  "f2 = (\<lambda>x. (x + 1))"
definition f3 :: "int => int" where
  "f3 = (\<lambda>x. (x + 1))"
definition f4 :: "int => int" where
  "f4 = (\<lambda>x. (x + 1))"
definition f5_multiarg :: "int => int => int" where
  "f5_multiarg = (\<lambda>y x. (x + y))"
definition f5_multiarg_applied :: "int" where
  "f5_multiarg_applied = (f5_multiarg 0 1)"
definition f5_curried :: "int => (int => int)" where
  "f5_curried = (\<lambda>x. (\<lambda>y. (x + y)))"
definition f5_curried_applied :: "int" where
  "f5_curried_applied = (f5_curried 0) 1"
definition f5_multiarg_variant :: "int => int => int" where
  "f5_multiarg_variant = (\<lambda>y x. (x + y))"

end