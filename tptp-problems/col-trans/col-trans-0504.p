include('col-axioms.ax').

fof(pipo,conjecture,
(! [A, B, C, IB, XB, IA, X] : ( (
 wd( A, B) &
 wd( B, C) &
  wd( A, C) &
   wd( IB, B) &
    wd( IA, A) &
     wd( XB, B) &
      col( B, A, IA) &
       col( IA, A, C) &
        col( B, X, A) &
         col( XB, X, B) &
          col( B, B, C) &
           col( A, XB, C) & col( B, XB, IB) ) => col( B, A, C))) 
).
