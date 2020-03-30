include('col-axioms.ax').

fof(pipo,conjecture,
(! [P, Q, S, X, Y] : ( (
 wd( P, X) &
 wd( S, X) &
  wd( Q, Y) &
   wd( S, Y) &
    wd( Q, S) &
     wd( P, S) &
      col( P, Q, S) & col( Q, Y, S) & col( P, X, S) ) => col( Q, S, X))) 
).
