include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, D, E, C, F] : ( (
 wd( A, B) &
 wd( B, E) &
  wd( A, E) &
   wd( A, B) &
    wd( A, D) &
     wd( B, A) &
      wd( A, F) &
       wd( B, F) &
        colH(A, B, E) &
         colH(A, B, D) & colH(B, A, F) & colH(A, C, F) ) => colH(A,  B,  C)))
).
