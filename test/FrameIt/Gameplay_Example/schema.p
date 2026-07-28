theory SimilarTriangles{
  //             D
  //           ,´|
  //          E  |
  //        ,´|  |
  //       A--B--C

  A: point
  B: point
  C: point
  D: point
  E: point
  AB: float
  AB_P:  |- dist(A)(B) == AB
  AC: float
  AC_P:  |- dist(A)(C) == AC
  BE: float
  BE_P: |- dist(B)(E) == BE
  are_similar: |- similar((D,A,C))((E,A,B)) 

  // The solution of the scroll. Recognizable by 
  // - starting with a double underscore
  // - having a definiens ?
  CD = AC * BE / AB
  CD_P: |- dist(C)(D) == CD = ???
  //__CD_Schema: |- __CD == (_AC * _BE / _AB) = ???
}

theory SimilarTriangles_Sigma{
  //             D
  //           ,´|
  //          E  |
  //        ,´|  |
  //       A--B--C

  A: point
  B: point
  C: point
  D: point
  E: point
  AB: (AB:float, |- dist(A)(B) == AB)
  AC: (AC:float, |- dist(A)(C) == AC)
  BE: (BE:float, |- dist(B)(E) == BE)
  are_similar: |- similar((D,A,C))((E,A,B)) 

  // The solution of the scroll. Recognizable by 
  // - starting with a double underscore
  CD: (CD:float, |- dist(C)(D) == CD)
  //schema_proof: |- dist(_C)(_D) == _AC(1) * _BE(1) / _AB(1) = ??? 
  //schema_app: |- __CD == (_AC(1) * _BE(1) / _AB(1), schema_proof) = ???
}