include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, D, F] : ( (
 wd( A, B) &
 wd( A, C) &
  wd( B, C) &
   wd( B, D) &
    wd( A, D) &
     wd( C, D) &
      wd( C, F) & wd( B, D) & col(A, B, C) & col(B, C, D) ) => col(A,  C,  D)))
).

