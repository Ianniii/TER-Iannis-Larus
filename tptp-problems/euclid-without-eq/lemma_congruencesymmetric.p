fof(cn_congruencereflexive,axiom, (! [A,B] : ((cong(A,B,A,B))))).
fof(cn_congruencetransitive,axiom, (! [B,C,D,E,P,Q] : ((cong(P,Q,B,C) & cong(P,Q,D,E)) => ((cong(B,C,D,E)))))).
fof(eq_excluded_middle,axiom, (! [A,B] : ((eq(A,B)) | (neq(A,B))))).
fof(cong_excluded_middle,axiom, (! [A,B,C,D] : ((cong(A,B,C,D)) | (ncong(A,B,C,D))))).
fof(lemma_congruencesymmetric,conjecture,(  ! [A,B,C,D] : ((cong(B,C,A,D)) => (cong(A,D,B,C))))).