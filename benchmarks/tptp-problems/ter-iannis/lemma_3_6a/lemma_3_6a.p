% ./larus -vcoq -m18 -i benchmarks/tptp-problems/ter-iannis/lemma_3_6a/lemma_3_6a.p
% with a hint and '-i', Larus can't find a proof

fof(axiom_betweennesssymmetry,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((betS(C,B,A)))))).
fof(axiom_innertransitivity,axiom, (! [A,B,C,D] : ((betS(A,B,D) & betS(B,C,D)) => ((betS(A,B,C)))))).
%fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((( B != C ) & ( A != B ) & ( A != C )))))).
fof(lemma_3_6a,conjecture,(! [A,B,C,D] : ((betS(A,B,C) & betS(A,C,D)) => ((betS(B,C,D)))))).


fof(hintname0, hint, _, _ , axiom_innertransitivity(_,_,_,_)).
%fof(hintname0, hint, _, _ , axiom_betweennesssymmetry(?,?,?)).
%fof(hintname0, hint, _, _ , lemma_betweennotequal(?,?,?)).