include('col-axioms.ax').

fof(pipo,conjecture,
(! [P, Q, A, B, C, Aprime, Bprime, Cprime] : ( (
 wd( P, Q) &
 wd( P, Aprime) &
  wd( P, Bprime) &
   wd( P, Cprime) &
    wd( A, Aprime) &
     wd( B, Bprime) &
      wd( C, Cprime) &
       wd( A, B) &
        wd( C, B) &
         wd( A, C) &
          wd( Aprime, Cprime) &
           wd( Aprime, Bprime) &
            wd( Cprime, Bprime) &
             wd( C, P) &
              wd( B, P) &
               wd( A, P) &
                wd( B, Cprime) &
                 wd( Bprime, C) &
                  wd( B, Aprime) &
                   wd( Bprime, A) &
                    col( P, Q, Aprime) &
                     col( P, Q, Bprime) &
                      col( P, Q, Cprime) &
                       col( A, B, C) & col( A, B, Bprime) ) => col( P, Aprime, Bprime))) 
).
