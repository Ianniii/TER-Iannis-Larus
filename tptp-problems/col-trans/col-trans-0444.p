include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, P, A, B, Q, C, Q1, Q2] : ( (
 wd( P, O) &
 wd( A, B) &
  wd( A, C) &
   wd( B, C) &
    wd( O, C) &
     wd( Q1, Q2) &
      col( O, A, B) &
       col( A, B, Q) &
        col( A, B, C) &
         col( Q1, Q2, C) & col( Q1, O, Q2) ) => col( A, B, Q1)))  ).
