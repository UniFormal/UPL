theory Test072
  imports Main
begin

definition t2 :: "int \<times> int" where
  "t2 = (1,2)"
definition t3 :: "int \<times> int \<times> int" where
  "t3 = (1,2,3)"
definition t4 :: "int \<times> int \<times> int \<times> int" where
  "t4 = (1,2,3,4)"
definition t5 :: "int \<times> int \<times> int \<times> int \<times> int" where
  "t5 = (1,2,3,4,5)"
definition t6 :: "int \<times> int \<times> int \<times> int \<times> int \<times> int" where
  "t6 = (1,2,3,4,5,6)"
definition t7 :: "int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int" where
  "t7 = (1,2,3,4,5,6,7)"
definition t8 :: "int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int" where
  "t8 = (1,2,3,4,5,6,7,8)"
definition t9 :: "int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int" where
  "t9 = (1,2,3,4,5,6,7,8,9)"
definition t10 :: "int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int \<times> int" where
  "t10 = (1,2,3,4,5,6,7,8,9,10)"
definition t_21 :: "int" where
  "t_21 = fst (t2)"
definition t_22 :: "int" where
  "t_22 = snd (t2)"
definition t_31 :: "int" where
  "t_31 = fst (t3)"
definition t_32 :: "int" where
  "t_32 = fst (snd (t3))"
definition t_33 :: "int" where
  "t_33 = snd (snd (t3))"
definition t_41 :: "int" where
  "t_41 = fst (t4)"
definition t_42 :: "int" where
  "t_42 = fst (snd (t4))"
definition t_43 :: "int" where
  "t_43 = fst (snd (snd (t4)))"
definition t_44 :: "int" where
  "t_44 = snd (snd (snd (t4)))"
definition t_51 :: "int" where
  "t_51 = fst (t5)"
definition t_52 :: "int" where
  "t_52 = fst (snd (t5))"
definition t_53 :: "int" where
  "t_53 = fst (snd (snd (t5)))"
definition t_54 :: "int" where
  "t_54 = fst (snd (snd (snd (t5))))"
definition t_55 :: "int" where
  "t_55 = snd (snd (snd (snd (t5))))"
definition t_61 :: "int" where
  "t_61 = fst (t6)"
definition t_62 :: "int" where
  "t_62 = fst (snd (t6))"
definition t_63 :: "int" where
  "t_63 = fst (snd (snd (t6)))"
definition t_64 :: "int" where
  "t_64 = fst (snd (snd (snd (t6))))"
definition t_65 :: "int" where
  "t_65 = fst (snd (snd (snd (snd (t6)))))"
definition t_66 :: "int" where
  "t_66 = snd (snd (snd (snd (snd (t6)))))"
definition t_71 :: "int" where
  "t_71 = fst (t7)"
definition t_72 :: "int" where
  "t_72 = fst (snd (t7))"
definition t_73 :: "int" where
  "t_73 = fst (snd (snd (t7)))"
definition t_74 :: "int" where
  "t_74 = fst (snd (snd (snd (t7))))"
definition t_75 :: "int" where
  "t_75 = fst (snd (snd (snd (snd (t7)))))"
definition t_76 :: "int" where
  "t_76 = fst (snd (snd (snd (snd (snd (t7))))))"
definition t_77 :: "int" where
  "t_77 = snd (snd (snd (snd (snd (snd (t7))))))"
definition t_81 :: "int" where
  "t_81 = fst (t8)"
definition t_82 :: "int" where
  "t_82 = fst (snd (t8))"
definition t_83 :: "int" where
  "t_83 = fst (snd (snd (t8)))"
definition t_84 :: "int" where
  "t_84 = fst (snd (snd (snd (t8))))"
definition t_85 :: "int" where
  "t_85 = fst (snd (snd (snd (snd (t8)))))"
definition t_86 :: "int" where
  "t_86 = fst (snd (snd (snd (snd (snd (t8))))))"
definition t_87 :: "int" where
  "t_87 = fst (snd (snd (snd (snd (snd (snd (t8)))))))"
definition t_88 :: "int" where
  "t_88 = snd (snd (snd (snd (snd (snd (snd (t8)))))))"
definition t_91 :: "int" where
  "t_91 = fst (t9)"
definition t_92 :: "int" where
  "t_92 = fst (snd (t9))"
definition t_93 :: "int" where
  "t_93 = fst (snd (snd (t9)))"
definition t_94 :: "int" where
  "t_94 = fst (snd (snd (snd (t9))))"
definition t_95 :: "int" where
  "t_95 = fst (snd (snd (snd (snd (t9)))))"
definition t_96 :: "int" where
  "t_96 = fst (snd (snd (snd (snd (snd (t9))))))"
definition t_97 :: "int" where
  "t_97 = fst (snd (snd (snd (snd (snd (snd (t9)))))))"
definition t_98 :: "int" where
  "t_98 = fst (snd (snd (snd (snd (snd (snd (snd (t9))))))))"
definition t_99 :: "int" where
  "t_99 = snd (snd (snd (snd (snd (snd (snd (snd (t9))))))))"
definition t_101 :: "int" where
  "t_101 = fst (t10)"
definition t_102 :: "int" where
  "t_102 = fst (snd (t10))"
definition t_103 :: "int" where
  "t_103 = fst (snd (snd (t10)))"
definition t_104 :: "int" where
  "t_104 = fst (snd (snd (snd (t10))))"
definition t_105 :: "int" where
  "t_105 = fst (snd (snd (snd (snd (t10)))))"
definition t_106 :: "int" where
  "t_106 = fst (snd (snd (snd (snd (snd (t10))))))"
definition t_107 :: "int" where
  "t_107 = fst (snd (snd (snd (snd (snd (snd (t10)))))))"
definition t_108 :: "int" where
  "t_108 = fst (snd (snd (snd (snd (snd (snd (snd (t10))))))))"
definition t_109 :: "int" where
  "t_109 = fst (snd (snd (snd (snd (snd (snd (snd (snd (t10)))))))))"
definition t_110 :: "int" where
  "t_110 = snd (snd (snd (snd (snd (snd (snd (snd (snd (t10)))))))))"

end