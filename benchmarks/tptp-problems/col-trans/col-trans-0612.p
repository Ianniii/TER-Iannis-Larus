include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C , T, P] : ( (
 wd( A, B) &
 wd( A, C) &
  wd( B, T) &
   wd( A, T) &
    wd( T, P) &
     col( A, B, P) & col( A, B, C) & col( A, C, T) ) => col( A, B, T))) 
).
