include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C , Q, R] : ( (
 wd( B, A) &
 wd( A, C) &
  wd( B, C) &
   wd( Q, A) &
    wd( Q, C) &
     wd( R, A) &
      wd( R, B) &
       col( C, A, B) & col( B, R, A) & col( C, Q, A) ) => col( A, B, Q))) 
).
