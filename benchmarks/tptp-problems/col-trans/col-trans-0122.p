include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, C0, P] : ( (
 wd( A, B) &
 wd( C, B) &
  wd( A, C) &
   wd( B, C0) &
    col( A, B, C0) & col( P, A, C0) & col( B, C0, C) ) => col( A, B, C)))
).

