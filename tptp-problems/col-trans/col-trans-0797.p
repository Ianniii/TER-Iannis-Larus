include('col-axioms.ax').

fof(pipo,conjecture,
(! [H, K, O, L, Hprime, Kprime, Oprime, Lprime, Kprimeprime, Lprimeprime, I, Iprime] : ( (
 wd( Oprime, Kprimeprime) &
 wd( Oprime, Kprime) &
  wd( Oprime, Lprimeprime) &
   wd( Oprime, Lprime) &
    wd( O, H) &
     wd( O, I) &
      wd( Oprime, Iprime) &
       wd( Iprime, Lprimeprime) &
        wd( O, K) &
         wd( O, L) &
          colH(Oprime,Kprime,Kprimeprime) &
           colH(Oprime,Lprime,Lprimeprime) &
            colH(Oprime,Iprime,Hprime) &
             colH(O, I, H) & colH(Hprime,Lprimeprime,Oprime) ) => colH(Hprime,Oprime,Lprime))) ).
