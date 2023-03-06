% ./larus -vcoq -m18 -l30 benchmarks/tptp-problems/ter-iannis/proposition_06/prop_06_hint4.p
% 8s
% length 15

fof(proposition_06a,axiom, (! [A,B,C] : ((triangle(A,B,C) & congA(A,B,C,A,C,B)) => ((~ (lt(A,C,A,B))))))).
fof(deftriangle,axiom, (! [A,B,C] : ((triangle(A,B,C)) => ((~ (col(A,B,C))))))).
fof(deftriangle2,axiom, (! [A,B,C] : ((~ (col(A,B,C))) => ((triangle(A,B,C)))))).
fof(lemma_collinearorder,axiom, (! [A,B,C] : ((col(A,B,C)) => ((col(B,A,C) & col(B,C,A) & col(C,A,B) & col(A,C,B) & col(C,B,A)))))).
fof(lemma_collinearorder2,axiom, (! [A,B,C] : ((~(col(A,B,C))) => (((~(col(B,A,C))) & (~(col(B,C,A))) & (~(col(C,A,B))) & (~(col(A,C,B))) & (~(col(C,B,A)))))))).
fof(lemma_equalanglessymmetric,axiom, (! [A,B,C,Xa,Xb,Xc] : ((congA(A,B,C,Xa,Xb,Xc)) => ((congA(Xa,Xb,Xc,A,B,C)))))).
fof(lemma_angledistinct,axiom, (! [A,B,C,Xa,Xb,Xc] : ((congA(A,B,C,Xa,Xb,Xc)) => ((( A != B ) & ( B != C ) & ( A != C ) & ( Xa != Xb ) & ( Xb != Xc ) & ( Xa != Xc )))))).
fof(lemma_trichotomy1,axiom, (! [A,B,C,D] : ((~ (lt(A,B,C,D)) & ~ (lt(C,D,A,B)) & ( A != B ) & ( C != D )) => ((cong(A,B,C,D)))))).
fof(proposition_06,conjecture,(! [A,B,C] : ((triangle(A,B,C) & congA(A,B,C,A,C,B)) => ((cong(A,B,A,C)))))).

fof(hintname0, hint, _, _, proposition_06a(0,1,2)).
fof(hintname1, hint, (~(col(0,1,2))), 2, _).
fof(hintname2, hint, (~(col(0,2,1))), 3, _).
fof(hintname5, hint, _, 8, lemma_equalanglessymmetric(0,1,2,0,2,1)).
fof(hintname3, hint, _, 10, lemma_angledistinct(0,2,1,0,1,2)).
fof(hintname4, hint, _, 11, lemma_trichotomy1(0,1,0,2)).