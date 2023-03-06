% ./larus -vcoq -m18 -l30 benchmarks/tptp-problems/ter-iannis/proposition_06/prop_06_hint1.p
% error

fof(proposition_06a,axiom, (! [A,B,C] : ((triangle(A,B,C) & congA(A,B,C,A,C,B)) => ((~ (lt(A,C,A,B))))))).
fof(deftriangle,axiom, (! [A,B,C] : ((triangle(A,B,C)) => ((~ (col(A,B,C))))))).
fof(deftriangle2,axiom, (! [A,B,C] : ((~ (col(A,B,C))) => ((triangle(A,B,C)))))).
fof(lemma_collinearorder,axiom, (! [A,B,C] : ((col(A,B,C)) => ((col(B,A,C) & col(B,C,A) & col(C,A,B) & col(A,C,B) & col(C,B,A)))))).
fof(lemma_equalanglessymmetric,axiom, (! [A,B,C,Xa,Xb,Xc] : ((congA(A,B,C,Xa,Xb,Xc)) => ((congA(Xa,Xb,Xc,A,B,C)))))).
fof(lemma_angledistinct,axiom, (! [A,B,C,Xa,Xb,Xc] : ((congA(A,B,C,Xa,Xb,Xc)) => ((( A != B ) & ( B != C ) & ( A != C ) & ( Xa != Xb ) & ( Xb != Xc ) & ( Xa != Xc )))))).
fof(lemma_trichotomy1,axiom, (! [A,B,C,D] : ((~ (lt(A,B,C,D)) & ~ (lt(C,D,A,B)) & ( A != B ) & ( C != D )) => ((cong(A,B,C,D)))))).
fof(proposition_06,conjecture,(! [A,B,C] : ((triangle(A,B,C) & congA(A,B,C,A,C,B)) => ((cong(A,B,A,C)))))).

fof(hintname0, hint, col(0,2,1) | (~(col(0,2,1))), 4, _).