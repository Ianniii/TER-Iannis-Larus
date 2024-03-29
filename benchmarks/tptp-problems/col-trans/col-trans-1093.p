include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, G, Gprime, Aprime, Bprime, I] : ( (
 wd( A, B) &
 wd( B, C) &
  wd( A, C) &
   wd( Bprime, A) &
    wd( Bprime, C) &
     wd( Aprime, B) &
      wd( Aprime, C) &
       wd( I, B) &
        wd( I, A) &
         wd( G, A) &
          wd( Aprime, Gprime) &
           wd( G, C) &
            wd( I, Aprime) &
             wd( I, Gprime) &
              wd( I, C) &
               wd( I, G) &
                wd( Gprime, A) &
                 wd( Gprime, G) &
                  col( G, A, Aprime) &
                   col( G, B, Bprime) &
                    col( G, I, C) &
                     col( I, Aprime, Gprime) &
                      col( I, A, B) &
                       col( Gprime, A, G) &
                        col( Bprime, A, C) & col( Aprime, B, C) ) => col( A, B, C))) 
).

