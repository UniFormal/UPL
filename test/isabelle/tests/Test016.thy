theory Test016
  imports Complex_Main
begin

definition t1 :: "unit" where
  "t1 = ()"
definition t2 :: "nat" where
  "t2 = 1"
definition t3 :: "nat \<times> int" where
  "t3 = (1,(- 1))"
definition t4 :: "nat \<times> int \<times> rat" where
  "t4 = (1,(- 1),0.5)"
definition t5 :: "nat \<times> int \<times> rat \<times> char list" where
  "t5 = (1,(- 1),0.5,''complex number'')"

end