% ./larus -vcoq -m18 benchmarks/tptp-problems/ter-iannis/lemma_ray2/lemma_ray2_b.p
% Error : proof not found

fof(defray,axiom, (! [A,B,C] : (? [X] : ((out(A,B,C)) => ((betS(X,A,C) & betS(X,A,B))))))).
fof(defray2,axiom, (! [A,B,C,X] : ((betS(X,A,C) & betS(X,A,B)) => ((out(A,B,C)))))).
fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((( B != C ) & ( A != B ) & ( A != C )))))).
fof(lemma_ray2,conjecture,(! [A,B,C] : ((out(A,B,C)) => ((( A != B )))))).


fof(hintname0, hint, _, _ , lemma_betweennotequal(?,?,?)).
%fof(hintname1, hint, betS(A,?,?) & betS(A,?,?), _ , _).