include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, P, Q, D, R1, R2] : ( (
 wd( A, B) &
 wd( B, C) &
  wd( A, C) &
   wd( P, Q) &
    wd( D, A) &
     wd( D, B) &
      wd( P, R1) &
       wd( Q, R1) &
        wd( D, R1) &
         wd( R1, R2) &
          wd( D, R2) &
           col( P, Q, D) &
            col( P, Q, R1) &
             col( R1, D, R2) & col( D, A, B) ) => col( P, Q, R2))) 
).
