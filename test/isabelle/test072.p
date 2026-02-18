module Test072 {

  // tuple positional access, projection
  t2: (int, int) = (1, 2)
  t3: (int, int, int) = (1, 2, 3)
  t4: (int, int, int, int) = (1, 2, 3, 4)
  t5: (int, int, int, int, int) = (1, 2, 3, 4, 5)
  t6: (int, int, int, int, int, int) = (1, 2, 3, 4, 5, 6)
  t7: (int, int, int, int, int, int, int) = (1, 2, 3, 4, 5, 6, 7)
  t8: (int, int, int, int, int, int, int, int) = (1, 2, 3, 4, 5, 6, 7, 8)
  t9: (int, int, int, int, int, int, int, int, int) = (1, 2, 3, 4, 5, 6, 7, 8, 9)
  t10: (int, int, int, int, int, int, int, int, int, int) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10)

  // Projections for t2
  t_21: int = t2(1)
  t_22: int = t2(2)

  // Projections for t3
  t_31: int = t3(1)
  t_32: int = t3(2)
  t_33: int = t3(3)

  // Projections for t4
  t_41: int = t4(1)
  t_42: int = t4(2)
  t_43: int = t4(3)
  t_44: int = t4(4)

  // Projections for t5
  t_51: int = t5(1)
  t_52: int = t5(2)
  t_53: int = t5(3)
  t_54: int = t5(4)
  t_55: int = t5(5)

  // Projections for t6
  t_61: int = t6(1)
  t_62: int = t6(2)
  t_63: int = t6(3)
  t_64: int = t6(4)
  t_65: int = t6(5)
  t_66: int = t6(6)

  // Projections for t7
  t_71: int = t7(1)
  t_72: int = t7(2)
  t_73: int = t7(3)
  t_74: int = t7(4)
  t_75: int = t7(5)
  t_76: int = t7(6)
  t_77: int = t7(7)

  // Projections for t8
  t_81: int = t8(1)
  t_82: int = t8(2)
  t_83: int = t8(3)
  t_84: int = t8(4)
  t_85: int = t8(5)
  t_86: int = t8(6)
  t_87: int = t8(7)
  t_88: int = t8(8)

  // Projections for t9
  t_91: int = t9(1)
  t_92: int = t9(2)
  t_93: int = t9(3)
  t_94: int = t9(4)
  t_95: int = t9(5)
  t_96: int = t9(6)
  t_97: int = t9(7)
  t_98: int = t9(8)
  t_99: int = t9(9)

  // Projections for t10
  t_101: int = t10(1)
  t_102: int = t10(2)
  t_103: int = t10(3)
  t_104: int = t10(4)
  t_105: int = t10(5)
  t_106: int = t10(6)
  t_107: int = t10(7)
  t_108: int = t10(8)
  t_109: int = t10(9)
  t_110: int = t10(10)
}