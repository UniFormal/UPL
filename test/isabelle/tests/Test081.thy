theory Test081
  imports Complex_Main
begin

definition int_div :: "int => int => rat" where
  "int_div = (\<lambda>y x. (Fract x y))"
definition rat_div :: "rat => rat => rat" where
  "rat_div = (\<lambda>y x. (x / y))"
definition comp_div :: "complex => complex => complex" where
  "comp_div = (\<lambda>y x. (x / y))"
definition real_div :: "real => real => real" where
  "real_div = (\<lambda>y x. (x / y))"

end