include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C , P, Q] : ( (
 wd( B, Q) &
 wd( P, Q) &
  wd( Q, C) &
   wd( P, C) &
    wd( B, C) &
     wd( A, P) &
      col( B, P, Q) & col( B, Q, C) & col( A, C, P) ) => col( P, Q, C))) 
).
