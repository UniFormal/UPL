theory SimilarTriangles{
  __label = " <ms>Intercept Theorem Scroll</ms>"
  __description = " <span>Given two
            <!-- <math data-slot-id='_are_similar'/>  -->similar
            triangles </span>
            <math>
                <mrow>
                    <ms> &xutri;<!-- △ --></ms>
                    <mi data-slot-id='_A' />
                    <mi data-slot-id='_B' />
                    <mi data-slot-id='_E' />
                </mrow>
            </math>
            and
            <math>
                <mrow>
                    <ms> &xutri;<!-- △ --></ms>
                    <mi data-slot-id='_A' />
                    <mi data-slot-id='_C' />
                    <mi data-slot-id='_D' />
                </mrow>
            </math>
            sharing the point 
            <math><mi data-slot-id='_A' /></math>. 
            The ratio
            <math>
                <mfrac>
                    <mi data-slot-id='_BE'/>
                    <mi data-slot-id='_AB'/>
                </mfrac>
            </math>
            between any two sides of
            <math>
                <mrow>
                    <ms> &xutri;<!-- △ --></ms>
                    <mi data-slot-id='_A' />
                    <mi data-slot-id='_B' />
                    <mi data-slot-id='_E' />
                </mrow>
            </math>
            is equal to the corresponding ratio
            <math>
                <mfrac>
                    <mi data-solution-id='_CD'/>
                    <mi data-slot-id='_AC'/>
                </mfrac>
            </math>
            in
            <math>
                <mrow>
                    <ms> &xutri;<!-- △ --></ms>
                    <mi data-slot-id='_A' />
                    <mi data-slot-id='_C' />
                    <mi data-slot-id='_D' />
                </mrow>
            </math>.
            Therefore
            <math >
                <mrow>
                    <mi data-solution-id='_CD'/>
                    <mo>&equals;</mo>
                    <mfrac>
                        <mi data-slot-id='_AC'/>
                        <mi data-slot-id='_AB'/>
                    </mfrac>
                    <mo>&times;</mo>
                    <mi data-slot-id='_BE'/>
                </mrow>
            </math>."
  __depiction=" <svg class='triangle' viewBox='-25 -25 400 300' version='1.1'
                xmlns='http://www.w3.org/2000/svg' xmlns:svg='http://www.w3.org/2000/svg' preserveAspectRatio='xMinYMin meet'>
                <g id='shape'
                    style='fill:none;stroke:#000000;stroke-linecap:butt;stroke-width:1;stroke-linejoin:miter;stroke-opacity:1'>
                    <path id='triangle' d='M 0,200 H 300 V 0 Z' />
                    <path id='triangle' d='M 100,200 v -67' />
                </g>
                <g id='labels' style='line-height:1.25;font-family:sans-serif;letter-spacing:0px;word-spacing:0px;font-size:medium;'>
                    <foreignObject id='pointA' x='-25' y='200' class='slotContainer'>
                        <math data-slot-id='_A' />
                    </foreignObject>
                    <foreignObject id='pointB' x='90' y='200' class='slotContainer'>
                        <math data-slot-id='_B' />
                    </foreignObject>
                    <foreignObject id='pointC' x='300' y='200' class='slotContainer'>
                        <math data-slot-id='_C' />
                    </foreignObject>
                    <foreignObject id='pointD' x='300' y='-25' class='slotContainer'>
                        <math data-slot-id='_D' />
                    </foreignObject>
                    <foreignObject id='pointE' x='90' y='100' class='slotContainer'>
                        <math data-slot-id='_E' />
                    </foreignObject>
                    <foreignObject id='distAB' x='40' y='200' class='slotContainer'>
                        <math data-slot-id='_AB' />
                    </foreignObject>
                    <foreignObject id='distAC' x='140' y='230' class='slotContainer'>
                        <math data-slot-id='_AC' />
                    </foreignObject>
                    <foreignObject id='distBE' x='110' y='150' class='slotContainer'>
                        <math data-slot-id='_BE' />
                    </foreignObject>
                    <foreignObject id='distDC' x='310' y='100' class='slotContainer'>
                        <math style='color:#008000' data-solution-id='_CD' />
                    </foreignObject>
                </g>
            </svg>"
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
  _are_similar: |- similar((_A,_C,_D))((_A,_B,_E))
  //are_similar_T: |- similar_T(triA _D _A _C)(triA _E _A _B)
  _CD:float
  _CD_P: |- dist _C _D  == _CD
  _Theorem: |- _AB *_CD == _AC *_BE = ???
}

// theory SimilarTriangles_Sigma{
//   //             D
//   //           ,´|
//   //          E  |
//   //        ,´|  |
//   //       A--B--C
// 
//   _A: point
//   _B: point
//   _C: point
//   _D: point
//   _E: point
//   _AB: (AB:float, |- dist(_A)(_B) == AB)
//   _AC: (AC:float, |- dist(_A)(_C) == AC)
//   _BE: (BE:float, |- dist(_B)(_E) == BE)
//   _are_similar: |- similar((_D,_A,_C))((_E,_A,_B)) 
// 
//   // The solution of the scroll. 
//   _CD: (CD:float, |- dist _C _D == CD)
//   //_CD_P: |- dist _C _D == _AC(1) * _BE(1) / _AB(1) = ??? 
//   //_Theorem: |- _CD == (_AC(1) * _BE(1) / _AB(1), _CD_P) = ???
// }
