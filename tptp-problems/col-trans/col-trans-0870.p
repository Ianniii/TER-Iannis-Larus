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
          colH(P, B, C) & colH(C, P, B) & colH(B, C, Q) ) => colH(C,  P,  Q)))
).
