include('col-axioms.ax').

fof(pipo,conjecture,
(! [O, X, Y, Z, Zprime] : ( (
 wd( O, X) &
 wd( Z, O) &
  wd( O, Zprime) &
   wd( Z, Zprime) &
    colH(Z,O,Zprime) & colH(O,Y,Zprime) & colH(Z,O,Zprime)) => colH(Y, O, Z))) ).
