include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B0, C, B, Bprime] : ( (
 wd( C, A) &
 wd( A, B) &
  wd( C, B) &
   wd( A, B0) &
    wd( B0, C) &
     wd( A, Bprime) &
      wd( B, Bprime) &
       wd( C, Bprime) & col( B, Bprime, C) & col( B, A, Bprime) ) => col( A, C, Bprime))) 
).
