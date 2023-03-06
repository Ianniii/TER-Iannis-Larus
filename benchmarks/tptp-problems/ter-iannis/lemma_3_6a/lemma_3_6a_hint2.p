% ./larus -vcoq -m18 benchmarks/tptp-problems/ter-iannis/lemma_3_6a/lemma_3_6a_hint2.p
% with the first hint, Larus can't find a proof

fof(axiom_betweennesssymmetry,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((betS(C,B,A)))))).
fof(axiom_innertransitivity,axiom, (! [A,B,C,D] : ((betS(A,B,D) & betS(B,C,D)) => ((betS(A,B,C)))))).
%fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((( B != C ) & ( A != B ) & ( A != C )))))).
fof(lemma_3_6a,conjecture,(! [A,B,C,D] : ((betS(A,B,C) & betS(A,C,D)) => ((betS(B,C,D)))))).


fof(hintname0, hint, betS(3,2,1), 2 , axiom_innertransitivity(3,2,1,0)).
%fof(hintname0, hint, _, _ , axiom_betweennesssymmetry(?,?,?)).
%fof(hintname0, hint, _, _ , lemma_betweennotequal(?,?,?)).