include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, X, C , D, U, V] : ( (
 wd( U, X) &
 wd( X, V) &
  wd( U, A) &
   wd( A, V) &
    wd( U, V) &
     wd( C, D) &
      wd( X, A) & col( U, A, V) & col( U, X, V) ) => col( A, X, V))) 
).
