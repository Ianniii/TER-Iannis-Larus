include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, E, Eprime, A, B, C, Bprime] : ( (
 wd( O, E) &
 wd( E, Eprime) &
  wd( O, Eprime) &
   wd( O, Bprime) &
    wd( O, B) &
     col( O, E, A) & col( O, E, B) & col( O, E, C) ) => col( O, B, A))) 
).
