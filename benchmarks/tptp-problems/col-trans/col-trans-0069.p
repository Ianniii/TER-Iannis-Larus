include('col-axioms.ax').

fof(pipo,conjecture,
(! [P, Q, S , X, Z] : ( (
 wd( P, X) &
 wd( S, X) &
  wd( S, Z) &
   wd( Q, Z) &
    wd( X, Z) &
     wd( P, Q) &
      wd( Q, S) &
       wd( P, S) &
        wd( X, Q) &
         col( Z, Z, P) &
          col( X, Z, Q) &
           col( Q, Z, S) & col( P, X, S) ) => col( P, Q, S)))  ).
