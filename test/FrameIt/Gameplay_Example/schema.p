theory _SimilarTriangles{
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
  // - starting with a double underscore
  // - having a definiens ?
  __CD = _AC * _BE / _AB
  __CD_P: |- dist(_C)(_D) == __CD = ???
  //__CD_Schema: |- __CD == (_AC * _BE / _AB) = ???
}

theory _SimilarTriangles_Sigma{
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
  _AB: (AB:float, |- dist(_A)(_B) == AB)
  _AC: (AC:float, |- dist(_A)(_C) == AC)
  _BE: (BE:float, |- dist(_B)(_E) == BE)
  _are_similar: |- similar((_D,_A,_C))((_E,_A,_B)) 

  // The solution of the scroll. Recognizable by 
  // - starting with a double underscore
  __CD: (CD:float, |- dist(_C)(_D) == CD)
  //schema_proof: |- dist(_C)(_D) == _AC(1) * _BE(1) / _AB(1) = ??? 
  //schema_app: |- __CD == (_AC(1) * _BE(1) / _AB(1), schema_proof) = ???
}