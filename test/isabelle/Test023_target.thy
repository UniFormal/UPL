theory Test023_target
  imports Main "HOL-Library.Multiset"
begin

definition m1 :: "int multiset" where "m1 = {#1, 2, 2, 3#}"
definition m2 :: "int multiset" where "m2 = m1 + {#1#}"     (* Adds another 1 *)
definition m3 :: "int multiset" where "m3 = m1 - {#2#}"     (* Removes one '2' *)
definition m4 :: "int multiset" where "m4 = mset [1, 1, 2]" (* List to multiset *)

value m1
end
