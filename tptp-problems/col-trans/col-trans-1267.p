include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, E, Eprime, A, Aprime, B, C] : ( (
 wd( B, O) &
 wd( Aprime, O) &
  wd( O, E) &
   wd( O, Eprime) &
    wd( E, Eprime) &
     wd( C, O) &
      col( O, E, A) &
       col( O, E, B) &
        col( O, E, C) &
         col( O, E, Aprime) &
          col( O, Eprime, C) & col( O, Eprime, C) ) => col( O, E, Eprime)))  ).
