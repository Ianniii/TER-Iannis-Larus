fof(lemma_3_6a,axiom, (! [A,B,C,D] : ((betS(A,B,C) & betS(A,C,D)) => ((betS(B,C,D)))))).
fof(axiom_betweennessidentity,axiom, (! [A,B] : ((nbetS(A,B,A))))).
fof(axiom_innertransitivity,axiom, (! [A,B,C,D] : ((betS(A,B,D) & betS(B,C,D)) => ((betS(A,B,C)))))).
fof(lemma_betweennotequal,conjecture,(  ! [A,B,C] : ((betS(A,B,C)) => (neq(B,C) & neq(A,B) & neq(A,C))))).