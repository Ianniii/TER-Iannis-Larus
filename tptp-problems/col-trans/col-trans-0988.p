include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, Aprime, Bprime, Cprime, O] : ( (
 wd( B, O) &
 wd( A, O) &
  wd( C, O) &
   wd( Bprime, O) &
    wd( Aprime, O) &
     wd( Cprime, O) &
      wd( Aprime, Bprime) &
       wd( A, Aprime) &
        wd( Aprime, Cprime) &
         wd( A, Cprime) &
          wd( B, C) &
           wd( Bprime, Cprime) &
            wd( A, C) &
             wd( A, B) &
              wd( Aprime, C) &
               wd( A, Bprime) &
                wd( B, Aprime) &
                 wd( B, Bprime) &
                  wd( C, Cprime) &
                   col( O, A, Aprime) &
                    col( O, B, Bprime) &
                     col( O, C, Cprime) & col( O, Aprime, Cprime) ) => col( O, A, C))) 
).
