include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C , D, M] : ( (
 wd( B, D) &
 wd( A, C) &
  wd( M, C) &
   wd( M, B) &
    wd( M, D) &
     wd( A, M) &
      col( A, B, C) & col( A, M, C) & col( B, M, D) ) => col( C, D, A))) 
).
