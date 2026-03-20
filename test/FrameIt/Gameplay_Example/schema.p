theory _SimilarTriangles{
  //             D
  //           ,´|
  //          E  |
  //        ,´|  |
  //       C--B--X
  
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
  _AB_P:  |- dist(_A)(_B) == _AB
  _AC: float
  _AC_P:  |- dist(_A)(_C) == _AC
  _BE: float
  _BE_P: |- dist(_B)(_E) == _BE
  _are_similar: |- similar((_D,_A,_C))((_E,_A,_B)) 

  // The solution of the scroll. Recognizable by 
  // - having a definiens
  // - starting with a double underscore
  __CD = _AC * _BE / _AB
  __CD_P: |- dist(_C)(_D) == __CD = ???
}