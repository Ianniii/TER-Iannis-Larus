include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, Aprime, Bprime] : ( (
 wd( A, Aprime) &
 wd( B, Bprime) &
  wd( B, A) &
   wd( B, Aprime) & col( A, B, Bprime) & col( Aprime, B, Bprime) ) => col( B, A, Aprime)))
).
