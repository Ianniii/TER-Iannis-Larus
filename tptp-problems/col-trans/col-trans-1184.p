include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, E, Eprime, A, Aprime] : ( (
 wd( A, O) &
 wd( O, E) &
  wd( E, Eprime) &
   wd( O, Eprime) &
    wd( A, Aprime) &
     col( O, E, A) &
      col( O, Eprime, Aprime) & col( O, Eprime, A) ) => col( O, E, Eprime)))  ).
