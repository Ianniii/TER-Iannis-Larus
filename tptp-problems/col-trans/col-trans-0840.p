include('col-axioms.ax').

fof(pipo,conjecture,
(! [A Aprime, B Bprime, C, Cprime, D, Dprime] : ( (
 wd( A, D) &
 wd( Aprime, Dprime) &
  wd( B, D) &
   wd( Bprime, Dprime) &
    wd( C, D) &
     wd( Cprime, Dprime) &
      wd( A, B) &
       wd( B, C) &
        wd( A, C) &
         wd( Aprime, Bprime) &
          wd( Bprime, Cprime) &
           wd( Aprime, Cprime) &
            wd( Aprime, Bprime) &
             wd( Bprime, Cprime) &
              wd( Aprime, Cprime) &
               wd( Aprime, Dprime) &
                colH(A, B, C) &
                 colH(A, B, C) &
                  colH(Aprime,Bprime,Cprime) &
                   colH(Aprime,Bprime,Cprime) & colH(Aprime,Cprime,Dprime) & ColH Aprime Bprime Dprime
).
