include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, A, B, Aprime, Bprime] : ( (
 wd( A, B) &
 wd( Aprime, Bprime) &
  wd( O, A) &
   wd( O, Aprime) &
    wd( A, Aprime) &
     wd( B, Bprime) &
      wd( A, Bprime) &
       wd( B, Aprime) &
        col( O, A, B) &
         col( O, Aprime, Bprime) &
          col( A, Aprime, Bprime) & col( B, Aprime, Bprime) ) => col( O, A, Aprime))) 
).
