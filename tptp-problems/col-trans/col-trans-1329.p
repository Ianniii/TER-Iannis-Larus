include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, E, Eprime, A, B, C, D] : ( (
 wd( C, O) &
 wd( O, E) &
  wd( O, Eprime) &
   wd( E, Eprime) &
    wd( A, O) &
     wd( B, O) &
      wd( D, O) &
       wd( O, Eprime) &
        wd( E, Eprime) &
         col( O, E, A) &
          col( O, E, B) &
           col( O, E, C) &
            col( O, E, D) & col( O, Eprime, B) ) => col( O, E, Eprime))) 
).
