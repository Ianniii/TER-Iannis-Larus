include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, Aprime, A0, C0] : ( (
 wd( B, A) &
 wd( A, Aprime) &
  wd( A, A0) &
   wd( B, A0) &
    wd( C, B) &
     wd( C, C0) &
      wd( B, C0) &
       wd( B, Aprime) &
        col( B, C, Aprime) &
         col( C, B, C0) & col( A, B, A0) ) => col( Aprime, B, C0)))  ).
