% ./larus -vcoq -m30 -l100 benchmarks/tptp-problems/ter-iannis/proposition_11/prop_11_hint4_3.p
% 32s
% length 4

fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((( B != C ) & ( A != B ) & ( A != C )))))).
fof(lemma_extension,axiom, (! [A,B,P,Q] : (? [X] : ((( A != B ) & ( P != Q )) => ((betS(A,B,X) & cong(B,X,P,Q))))))).
fof(proposition_11_int,conjecture,(! [A,B,C] : (?[E] : ((betS(A,C,B)) => ((betS(A,C,E) & cong(C,E,A,C))))))).

fof(hintname, _, _, lemma_betweennotequal(0,2,1)).
%fof(hintname0, _, _, lemma_extension(0,2,0,2)).