theory Test070_target
  imports Main
begin

definition t2 :: "int × int" where
  "t2 = (1, 2)"

definition t3 :: "int × int × int" where
  "t3 = (1, 2, 3)"

definition t4 :: "int × int × int × int" where
  "t4 = (1, 2, 3, 4)"

definition t5 :: "int × int × int × int × int" where
  "t5 = (1, 2, 3, 4, 5)"

definition t6 :: "int × int × int × int × int × int" where
  "t6 = (1, 2, 3, 4, 5, 6)"

definition t7 :: "int × int × int × int × int × int × int" where
  "t7 = (1, 2, 3, 4, 5, 6, 7)"

definition t8 :: "int × int × int × int × int × int × int × int" where
  "t8 = (1, 2, 3, 4, 5, 6, 7, 8)"

definition t9 :: "int × int × int × int × int × int × int × int × int" where
  "t9 = (1, 2, 3, 4, 5, 6, 7, 8, 9)"

definition t10 :: "int × int × int × int × int × int × int × int × int × int" where
  "t10 = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10)"

(* Projections for t2 *)
definition t2_1 :: int where "t2_1 = fst t2"
definition t2_2 :: int where "t2_2 = snd t2"

(* Projections for t3 *)
definition t3_1 :: int where "t3_1 = fst t3"
definition t3_2 :: int where "t3_2 = fst (snd t3)"
definition t3_3 :: int where "t3_3 = snd (snd t3)"

(* Projections for t4 *)
definition t4_1 :: int where "t4_1 = fst t4"
definition t4_2 :: int where "t4_2 = fst (snd t4)"
definition t4_3 :: int where "t4_3 = fst (snd (snd t4))"
definition t4_4 :: int where "t4_4 = snd (snd (snd t4))"

(* Projections for t5 *)
definition t5_1 :: int where "t5_1 = fst t5"
definition t5_2 :: int where "t5_2 = fst (snd t5)"
definition t5_3 :: int where "t5_3 = fst (snd (snd t5))"
definition t5_4 :: int where "t5_4 = fst (snd (snd (snd t5)))"
definition t5_5 :: int where "t5_5 = snd (snd (snd (snd t5)))"

(* Projections for t6 *)
definition t6_1 :: int where "t6_1 = fst t6"
definition t6_2 :: int where "t6_2 = fst (snd t6)"
definition t6_3 :: int where "t6_3 = fst (snd (snd t6))"
definition t6_4 :: int where "t6_4 = fst (snd (snd (snd t6)))"
definition t6_5 :: int where "t6_5 = fst (snd (snd (snd (snd t6))))"
definition t6_6 :: int where "t6_6 = snd (snd (snd (snd (snd t6))))"

(* Projections for t7 *)
definition t7_1 :: int where "t7_1 = fst t7"
definition t7_2 :: int where "t7_2 = fst (snd t7)"
definition t7_3 :: int where "t7_3 = fst (snd (snd t7))"
definition t7_4 :: int where "t7_4 = fst (snd (snd (snd t7)))"
definition t7_5 :: int where "t7_5 = fst (snd (snd (snd (snd t7))))"
definition t7_6 :: int where "t7_6 = fst (snd (snd (snd (snd (snd t7)))))"
definition t7_7 :: int where "t7_7 = snd (snd (snd (snd (snd (snd t7)))))"

(* Projections for t8 *)
definition t8_1 :: int where "t8_1 = fst t8"
definition t8_2 :: int where "t8_2 = fst (snd t8)"
definition t8_3 :: int where "t8_3 = fst (snd (snd t8))"
definition t8_4 :: int where "t8_4 = fst (snd (snd (snd t8)))"
definition t8_5 :: int where "t8_5 = fst (snd (snd (snd (snd t8))))"
definition t8_6 :: int where "t8_6 = fst (snd (snd (snd (snd (snd t8)))))"
definition t8_7 :: int where "t8_7 = fst (snd (snd (snd (snd (snd (snd t8))))))"
definition t8_8 :: int where "t8_8 = snd (snd (snd (snd (snd (snd (snd t8))))))"

(* Projections for t9 *)
definition t9_1 :: int where "t9_1 = fst t9"
definition t9_2 :: int where "t9_2 = fst (snd t9)"
definition t9_3 :: int where "t9_3 = fst (snd (snd t9))"
definition t9_4 :: int where "t9_4 = fst (snd (snd (snd t9)))"
definition t9_5 :: int where "t9_5 = fst (snd (snd (snd (snd t9))))"
definition t9_6 :: int where "t9_6 = fst (snd (snd (snd (snd (snd t9)))))"
definition t9_7 :: int where "t9_7 = fst (snd (snd (snd (snd (snd (snd t9))))))"
definition t9_8 :: int where "t9_8 = fst (snd (snd (snd (snd (snd (snd (snd t9)))))))"
definition t9_9 :: int where "t9_9 = snd (snd (snd (snd (snd (snd (snd (snd t9)))))))"

(* Projections for t10 *)
definition t10_1 :: int where "t10_1 = fst t10"
definition t10_2 :: int where "t10_2 = fst (snd t10)"
definition t10_3 :: int where "t10_3 = fst (snd (snd t10))"
definition t10_4 :: int where "t10_4 = fst (snd (snd (snd t10)))"
definition t10_5 :: int where "t10_5 = fst (snd (snd (snd (snd t10))))"
definition t10_6 :: int where "t10_6 = fst (snd (snd (snd (snd (snd t10)))))"
definition t10_7 :: int where "t10_7 = fst (snd (snd (snd (snd (snd (snd t10))))))"
definition t10_8 :: int where "t10_8 = fst (snd (snd (snd (snd (snd (snd (snd t10)))))))"
definition t10_9 :: int where "t10_9 = fst (snd (snd (snd (snd (snd (snd (snd (snd t10))))))))"
definition t10_10 :: int where "t10_10 = snd (snd (snd (snd (snd (snd (snd (snd (snd t10))))))))"


end