include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, D, P, Q, R, Z, T, I, X0] : ( (
 wd( A, C) &
 wd( P, Q) &
  wd( C, D) &
   wd( R, C) &
    wd( A, B) &
     wd( Q, R) &
      wd( T, Z) &
       wd( C, Q) &
        wd( P, C) &
         wd( A, T) &
          wd( I, Z) &
           wd( I, C) &
            wd( Z, C) &
             wd( R, I) &
              wd( X0, I) &
               wd( X0, C) &
                col( I, X0, Z) &
                 col( A, Z, T) &
                  col( P, R, Q) &
                   col( C, I, X0) & col( C, R, Z) ) => col( C, R, I))) 
).
