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
       wd( Pprime, A) &
        col( B, P, Pprime) &
         col( T, B, Pprime) & col( A, B, T) ) => col( Pprime, B, A)))  ).
