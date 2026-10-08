theory InterceptTheorem{
  //             D
  //           ,´|
  //          E  |
  //        ,´|  |
  //       A--B--C
  _A: point
  _B: point
  _C: point
  _D: point
  _E: point
  _AB: float
  _AB_P: |- dist(_A)(_B) == _AB
  _AC: float
  _AC_P: |- dist(_A)(_C) == _AC
  _BE: float
  _BE_P: |- dist(_B)(_E) == _BE
  _are_similar: |- similar((_D,_A,_C))((_E,_A,_B))
  _CD = _AC * _BE / _AB
  _CD_P: |- dist(_C)(_D) == _CD = ???
}
