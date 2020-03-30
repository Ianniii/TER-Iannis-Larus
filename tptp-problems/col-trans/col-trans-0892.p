include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, P, Q, I] : ( (
 wd( I, B) &
 wd( B, A) &
  wd( I, A) &
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
             wd( C, I) &
              colH(I, B, A) & colH(A, B, I) & colH(A, C, I) ) => colH(A,  B,  C)))
).
