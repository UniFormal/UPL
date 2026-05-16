// All regional names in a schema start with an underscore. This way there cannot be a name-clash
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
  _AB_P:  |- dist(_A)(_B) == _AB
  _AC: float
  _AC_P:  |- dist(_A)(_C) == _AC
  _BE: float
  _BE_P: |- dist(_B)(_E) == _BE
  // Adding a new Gadget to Unity to measure similarity, is more effort than gain
  //_are_similar: |- similar((_D,_A,_C))((_E,_A,_B)) 

  // For now there is a dedicated solution with a definiens; 
  // This should be replaced by the solver
  _CD = _AC * _BE / _AB
  _CD_P: |- dist(_C)(_D) == _CD = ???
  //__CD_Sol: |- _CD == (_AC * _BE / _AB) = ???
}

theory InterceptTheorem_Sigma{
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

  _CD: (CD:float, |- dist(_C)(_D) == CD)
  //schema_proof: |- dist(_C)(_D) == _AC(1) * _BE(1) / _AB(1) = ??? 
  //schema_app: |- _CD == (_AC(1) * _BE(1) / _AB(1), schema_proof) = ???
}