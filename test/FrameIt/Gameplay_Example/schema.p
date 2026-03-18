theory _SimilarTriangles{
  //             A
  //           ,´|
  //          B  |
  //        ,´|  |
  //       C--D--E

  _A: point
  _B: point
  _C: point
  _D: point
  _E: point
  _CD: float
  _CD_P:  |- dist(_C)(_D) == _CD
  _CE: float
  _CE_P:  |- dist(_C)(_E) == _CE
  _DB: float
  _DB_P: |- dist(_D)(_B) == _DB
  _are_similar: |- similar((_A,_C,_E))((_B,_C,_D)) 

  // The solution of the scroll. Recognizable by 
  // - having a definiens
  // - starting with a double underscore
  __EA = _CE * _DB / _CD
  __EA_P: |- dist(_E)(_A) == __EA = ???
}