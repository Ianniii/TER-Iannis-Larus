include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C , D, E, F] : ( (
 wd( E, F) &
 wd( A, B) &
  wd( C, D) & col( E, F, C) & col( E, F, D) ) => col( C, D, F)))  ).
