theory SimilarTriangles{
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
  _AB_P:  |- dist _A _B == _AB
  _AC: float
  _AC_P:  |- dist _A _C  == _AC
  _BE: float
  _BE_P: |- dist _B _E  == _BE
  _are_similar: |- similar((_D,_A,_C))((_E,_A,_B))
  //are_similar_T: |- similar_T(triA _D _A _C)(triA _E _A _B) 
 
  // Currently there is a solution of the schema, recognisable by its definiens.
  // But this will be phased out by the Solver using `_Theorem` below to solve for any of the distances
  _CD = _AC * _BE / _AB
  _CD_P: |- dist _C _D  == _CD = ???
  _Theorem: |- _CD == (_AC * _BE / _AB) = ???
}

theory SimilarTriangles_Sigma{
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

  // The solution of the scroll. 
  _CD: (CD:float, |- dist _C _D == CD)
  //_CD_P: |- dist _C _D == _AC(1) * _BE(1) / _AB(1) = ??? 
  //_Theorem: |- _CD == (_AC(1) * _BE(1) / _AB(1), _CD_P) = ???
}
