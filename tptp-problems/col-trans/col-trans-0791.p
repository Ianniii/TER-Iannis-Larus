include('col-axioms.ax').

fof(pipo,conjecture,
(! [H, O, Hprime, Oprime, Lprime, Lprimeprime, I] : ( (
 wd( Oprime, Lprimeprime) &
 wd( Oprime, Lprime) &
  wd( O, H) &
   wd( O, I) &
    wd( Oprime, Lprimeprime) &
     wd( Oprime, Lprimeprime) &
      wd( Oprime, Hprime) & colH(Oprime,Lprime,Lprimeprime) & colH(Oprime,Hprime,Lprimeprime) ) => colH(Hprime,Oprime,Lprime)))
).
