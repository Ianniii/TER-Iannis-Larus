fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((( B != C ) & ( A != B ) & ( A != C )))))).
fof(axiom_nocollapse,axiom, (! [A,B,C,D] : ((( A != B ) & cong(A,B,C,D)) => ((( C != D )))))).
fof(lemma_localextension,axiom, (! [A,B,Q] : (? [X] : ((( A != B ) & ( B != Q )) => ((betS(A,B,X) & cong(B,X,B,Q))))))).
fof(lemma_congruencesymmetric,axiom, (! [A,B,C,D] : ((cong(B,C,A,D)) => ((cong(A,D,B,C)))))).
fof(cn_congruencetransitive,axiom, (! [B,C,D,E,P,Q] : ((cong(P,Q,B,C) & cong(P,Q,D,E)) => ((cong(B,C,D,E)))))).
fof(axiom_5_line,axiom, (! [A,B,C,D,E,F,G,H] : ((betS(A,B,C) & betS(E,F,G) & cong(B,C,F,G) & cong(A,D,E,H) & cong(B,D,F,H) & cong(A,B,E,F)) => ((cong(D,C,H,G)))))).
fof(lemma_betweennesspreserved,conjecture,(! [A,B,C,Xa,Xb,Xc] : ((cong(A,B,Xa,Xb) & cong(A,C,Xa,Xc) & cong(B,C,Xb,Xc) & betS(A,B,C)) => ((betS(Xa,Xb,Xc)))))).
