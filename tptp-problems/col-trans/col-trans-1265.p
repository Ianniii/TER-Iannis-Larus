include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, E, Eprime, A, Aprime, B, C, Bprime] : ( (
 wd( B, O) &
 wd( Aprime, O) &
  wd( O, E) &
   wd( E, Eprime) &
    wd( O, Eprime) &
     wd( B, Bprime) &
      col( O, E, A) &
       col( O, E, B) &
        col( O, E, C) &
         col( O, E, Aprime) &
          col( O, Eprime, Bprime) & col( O, Eprime, B) ) => col( O, E, Eprime)))  ).
