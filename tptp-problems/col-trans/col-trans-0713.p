include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C , D] : ( (
 wd( A, B) &
 wd( C, D) &
  wd( C, D) & col( A, C, D) & col( B, C, D) ) => col( A, B, D)))  ).
