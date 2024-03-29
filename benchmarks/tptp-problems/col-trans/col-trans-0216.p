include('col-axioms.ax').

fof(pipo,conjecture,
(! [A1, A2, B1, B2, C1, C2, D1, D2, IAB, IAC, IBD, P1, R1, I ] : ( (
 wd( IAB, IAC) &
 wd( IAB, IBD) &
  wd( C1, P1) &
   wd( C2, P1) &
    wd( IAC, P1) &
     wd( D1, R1) &
      wd( D2, R1) &
       wd( IBD, R1) &
        wd( IAC, IBD) &
         wd( B1, B2) &
          wd( D1, D2) &
           wd( A1, A2) &
            wd( C1, C2) &
             wd( B1, C1) &
              wd( B1, C2) &
               wd( B2, C1) &
                wd( B2, C2) &
                 wd( A1, D1) &
                  wd( A1, D2) &
                   wd( A2, D1) &
                    wd( A2, D2) &
                     col( A1, A2, IAB) &
                      col( B1, B2, IAB) &
                       col( A1, A2, IAC) &
                        col( C1, C2, IAC) &
                         col( B1, B2, IBD) &
                          col( D1, D2, IBD) &
                           col( IAB, IAC, A1) &
                            col( IAB, IAC, A2) &
                             col( IAB, IBD, B1) &
                              col( IAB, IBD, B2) &
                               col( C1, C2, P1) &
                                col( D1, D2, R1) &
                                 col( IAC, P1, I) &
                                  col( IBD, R1, I) ) => col( C1, C2, I))) 
).

