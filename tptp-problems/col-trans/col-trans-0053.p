include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, X , Y, T] : ( (
 wd( X, Y) &
 wd( A, T) &
  wd( Y, A) &
   wd( A, B) &
    wd( Y, B) &
     wd( X, A) &
      wd( X, B) &
       col( T, A, B) & col( A, X, Y) & col( X, T, Y) ) => col( X, A, B))) 
).
