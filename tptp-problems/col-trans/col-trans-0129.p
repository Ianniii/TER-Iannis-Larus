include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, P, Q, Q0, R] : ( (
 wd( A, B) &
 wd( C, B) &
  wd( P, B) &
   wd( A, C) &
    wd( P, Q) &
     wd( B, Q) &
      wd( B, Q0) &
       wd( P, A) &
        wd( P, Q0) &
         wd( A, Q0) &
          col( B, C, P) &
           col( Q, P, Q0) &
            col( R, B, A) & col( P, R, Q0) ) => col( P, Q, R))) 
).
