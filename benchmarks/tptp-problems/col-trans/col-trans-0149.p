include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, P, T, Pprime] : ( (
 wd( P, T) &
 wd( B, T) &
  wd( P, B) &
   wd( A, B) &
    wd( A, C) &
     wd( C, B) &
      wd( Pprime, B) &
       col( B, P, Pprime) &
        col( Pprime, B, A) & col( Pprime, B, C) ) => col( A, B, C)))  ).
