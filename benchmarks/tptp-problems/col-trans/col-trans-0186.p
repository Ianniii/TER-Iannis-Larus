include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, Aprime, Cprime] : ( (
 wd( B, Aprime) &
 wd( B, Cprime) &
  wd( A, Aprime) &
   wd( C, Cprime) &
    wd( Aprime, Cprime) &
     wd( Cprime, A) &
      wd( B, C) &
       wd( B, A) &
        col( A, B, C) &
         col( Aprime, B, Cprime) &
          col( A, C, Cprime) & col( Aprime, C, Cprime) ) => col( Aprime, Cprime, A))) 
).
