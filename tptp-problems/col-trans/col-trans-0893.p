include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, P, Q] : ( (
 wd( P, Q) &
 wd( A, B) &
  wd( A, C) &
   wd( B, C) &
    wd( A, P) &
     wd( A, Q) &
      wd( B, P) &
       wd( B, Q) &
        wd( C, P) &
         wd( C, Q) &
          colH(P, A, B) & colH(B, P, A) & colH(A, B, Q) ) => colH(A,  P,  Q)))
).
