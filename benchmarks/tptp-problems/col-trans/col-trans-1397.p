include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, E, Eprime, A, B, C, D, U, Xu, Du, Bprime, Dprime, Dprimeprime] : ( (
 wd( U, O) &
 wd( O, E) &
  wd( O, Eprime) &
   wd( E, Eprime) &
    wd( A, O) &
     wd( B, O) &
      wd( C, O) &
       wd( D, O) &
        wd( U, Eprime) &
         wd( A, Eprime) &
          wd( O, Xu) &
           wd( Dprimeprime, O) &
            wd( D, Du) &
             col( O, E, A) &
              col( O, E, B) &
               col( O, E, C) &
                col( O, E, D) &
                 col( O, E, U) &
                  col( O, Eprime, O) &
                   col( O, E, Xu) &
                    col( O, A, Eprime) &
                     col( Xu, A, Eprime) &
                      col( O, Eprime, Du) &
                       col( O, Eprime, Bprime) &
                        col( O, Eprime, Dprime) &
                         col( O, Eprime, Dprimeprime) ) => col( O, E, Eprime))) 
).

