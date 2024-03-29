include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, E, Eprime, A, B, C, D, X, Bprime, Dprime] : ( (
 wd( C, O) &
 wd( A, O) &
  wd( B, O) &
   wd( D, O) &
    wd( O, E) &
     wd( O, Eprime) &
      wd( E, Eprime) &
       wd( Eprime, C) &
        wd( Bprime, O) &
         wd( C, Bprime) &
          wd( X, O) &
           wd( A, Dprime) &
            col( O, E, A) &
             col( O, E, B) &
              col( O, E, C) &
               col( O, E, D) &
                col( O, E, X) &
                 col( O, Eprime, O) &
                  col( O, Eprime, Bprime) &
                   col( O, Eprime, Dprime) &
                    col( E, C, Bprime) & col( O, C, Bprime) ) => col( O, E, Eprime))) 
).

