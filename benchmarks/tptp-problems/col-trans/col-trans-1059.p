include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, X1, X2, X3, D, F] : ( (
 wd( A, B) &
 wd( B, C) &
  wd( A, C) &
   wd( A, F) &
    wd( A, F) &
     wd( B, D) &
      wd( B, F) &
       wd( C, D) &
        wd( C, F) &
         wd( A, X3) &
          wd( B, X2) &
           wd( C, X1) &
            wd( D, F) &
             col( D, B, X2) &
              col( D, C, X1) &
               col( F, C, X1) &
                col( F, A, X3) &
                 col( F, A, X3) & col( F, B, X2) ) => col( C, D, B))) 
).
