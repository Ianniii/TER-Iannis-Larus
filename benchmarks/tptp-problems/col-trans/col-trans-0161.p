include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, Bprime] : ( (
 wd( A, Bprime) &
 wd( B, Bprime) &
  wd( A, C) &
   wd( C, Bprime) &
    wd( B, C) &
     wd( A, B) & col( A, B, C) & col( B, C, Bprime) ) => col( A, Bprime, C))) 
).

