include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, D, E, F, I] : ( (
 wd( A, B) &
 wd( A, C) &
  wd( B, C) &
   wd( B, D) &
    wd( A, D) &
     wd( C, D) &
      wd( C, F) &
       wd( A, I) &
        wd( I, E) &
         wd( A, E) &
          colH(A, B, C) &
           colH(A, I, E) & colH(C, D, F) & colH(C, F, I) ) => colH(C,  D,  I)))
).
