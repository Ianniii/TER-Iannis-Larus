include('col-axioms.ax').

fof(pipo,conjecture,
(! [A1, A2, B1, B2, C1, C2, D1, D2, IAB, IAC, IBD, E, F ] : ( (
 wd( IAB, IAC) &
 wd( IAB, IBD) &
  wd( IAB, F) &
   wd( IBD, F) &
    wd( IAB, E) &
     wd( IAC, E) &
      wd( B1, B2) &
       wd( D1, D2) &
        wd( A1, A2) &
         wd( C1, C2) &
          col( A1, A2, IAB) &
           col( B1, B2, IAB) &
            col( A1, A2, IAC) &
             col( C1, C2, IAC) &
              col( B1, B2, IBD) &
               col( D1, D2, IBD) &
                col( IBD, IAB, F) & col( IAC, IAB, E) ) => col( B1, B2, F))) 
).
