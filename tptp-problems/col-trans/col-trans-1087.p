include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, C, G, X, x0] : ( (
 wd( A, G) &
 wd( G, C) &
  wd( A, C) &
   wd( x0, A) &
    wd( x0, C) &
     wd( X, G) &
      wd( X, C) &
       col( G, A, X) & col( x0, A, C) & col( X, G, C) ) => col( A, G, C))) 
).
