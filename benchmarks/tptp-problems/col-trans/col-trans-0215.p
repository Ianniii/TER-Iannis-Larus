include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, A, B, C, Bprime] : ( (
 wd( A, Bprime) &
 wd( O, A) &
  wd( O, Bprime) &
   wd( A, B) &
    wd( B, C) &
     wd( B, Bprime) &
      wd( C, Bprime) &
       wd( O, C) &
        wd( O, B) &
         col( O, A, C) &
          col( A, B, C) &
           col( O, A, Bprime) & col( B, C, Bprime) ) => col( Bprime, O, C))) 
).

