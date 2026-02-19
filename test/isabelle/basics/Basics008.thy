theory Basics008
  imports Complex_Main
begin

definition int_add :: "int => int => int" where
  "int_add = (\<lambda>y x. (x + y))"
definition rat_add :: "rat => rat => rat" where
  "rat_add = (\<lambda>y x. (x + y))"
definition float_add :: "real => real => real" where
  "float_add = (\<lambda>y x. (x + y))"
definition float_add2 :: "real => real => real" where
  "float_add2 = (\<lambda>y x. (x + y))"
definition int_float_add :: "real => int => real" where
  "int_float_add = (\<lambda>y x. (x + y))"
definition int_div :: "int => int => rat" where
  "int_div = (\<lambda>y x. (Fract x y))"

end