theory Test053
  imports Main "HOL-Library.Multiset"
begin

definition s1 :: "bool" where
  "s1 = (1 \<in> {1,2,3})"
definition s2 :: "bool" where
  "s2 = (1 \<in> {1,2,3})"
definition s3 :: "bool" where
  "s3 = (1 \<in> {1,2,3})"

end