% ./larus -vcoq -m30 -l100 benchmarks/tptp-problems/ter-iannis/proposition_11/prop_11_hint1.p

fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((( B != C ) & ( A != B ) & ( A != C )))))).
fof(lemma_extension,axiom, (! [A,B,P,Q] : (? [X] : ((( A != B ) & ( P != Q )) => ((betS(A,B,X) & cong(B,X,P,Q))))))).
fof(proposition_01,axiom, (! [A,B] : (? [X] : ((( A != B )) => ((equilateral(A,B,X) & triangle(A,B,X))))))).
fof(defequilateral,axiom, (! [A,B,C] : ((equilateral(A,B,C)) => ((cong(A,B,B,C) & cong(B,C,C,A)))))).
fof(defequilateral2,axiom, (! [A,B,C] : ((cong(A,B,B,C) & cong(B,C,C,A)) => ((equilateral(A,B,C)))))).
fof(lemma_doublereverse,axiom, (! [A,B,C,D] : ((cong(A,B,C,D)) => ((cong(D,C,B,A) & cong(B,A,D,C)))))).
fof(lemma_congruenceflip,axiom, (! [A,B,C,D] : ((cong(A,B,C,D)) => ((cong(B,A,D,C) & cong(B,A,C,D) & cong(A,B,D,C)))))).
fof(defcollinear,axiom, (! [A,B,C] : ((col(A,B,C)) => ((( A = B )) | (( A = C )) | (( B = C )) | (betS(B,A,C)) | (betS(A,B,C)) | (betS(A,C,B)))))).
fof(defcollinear2a,axiom, (! [A,B,C] : ((( A = B )) => ((col(A,B,C)))))).
fof(defcollinear2b,axiom, (! [A,B,C] : ((( A = C )) => ((col(A,B,C)))))).
fof(defcollinear2c,axiom, (! [A,B,C] : ((( B = C )) => ((col(A,B,C)))))).
fof(defcollinear2d,axiom, (! [A,B,C] : ((betS(B,A,C)) => ((col(A,B,C)))))).
fof(defcollinear2e,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((col(A,B,C)))))).
fof(defcollinear2f,axiom, (! [A,B,C] : ((betS(A,C,B)) => ((col(A,B,C)))))).
fof(lemma_collinearorder,axiom, (! [A,B,C] : ((col(A,B,C)) => ((col(B,A,C) & col(B,C,A) & col(C,A,B) & col(A,C,B) & col(C,B,A)))))).
fof(lemma_collinearorder2,axiom, (! [A,B,C] : ((col(B,A,C) & col(B,C,A) & col(C,A,B) & col(A,C,B) & col(C,B,A))) => ((col(A,B,C))) )).
fof(deftriangle,axiom, (! [A,B,C] : ((triangle(A,B,C)) => ((~ (col(A,B,C))))))).
fof(deftriangle2,axiom, (! [A,B,C] : ((~ (col(A,B,C))) => ((triangle(A,B,C)))))).
fof(defrightangle,axiom, (! [A,B,C] : (? [X] : ((per(A,B,C)) => ((betS(A,B,X) & cong(A,B,X,B) & cong(A,C,X,C) & ( B != C ))))))).
fof(defrightangle2,axiom, (! [A,B,C,X] : ((betS(A,B,X) & cong(A,B,X,B) & cong(A,C,X,C) & ( B != C )) => ((per(A,B,C)))))).
fof(proposition_11,conjecture,(! [A,B,C] : (? [X] : ((betS(A,C,B)) => ((per(A,C,X))))))).


fof(hintname0,hint,_, 2, lemma_betweennotequal(0,1,2)).
fof(hintname1,hint,betS(0,2,?) & cong(2,?,0,2), 4, lemma_extension(0,2,0,2)).
fof(hintname2,hint,_, 5, lemma_betweennotequal(0,2,?)).
fof(hintname3,hint,triangle(0,A,?) & equilateral(0,A,?), 7, proposition_01(0,?)).
fof(hintname4,hint,_, 8, defequilateral(0,?,?)).
fof(hintname5,hint,_, 9, lemma_doublereverse(?,?,?,0)).
fof(hintname6,hint,_, 10, lemma_congruenceflip(0,?,?,?)).
fof(hintname7,hint, col(0,2,?), 13, defcollinear2e(0,2,?)).
%fof(hintname8,hint,_, 14, lemma_congruenceflip(0,?,?,?)).
fof(hintname10,hint,cong(2,0,?,2), 23, lemma_doublereverse(?,?,?,?)).
%fof(hintname9,hint,cong(0,2,?,0), 24, lemma_congruenceflip(0,?,?,?)).
fof(hintname11,hint,per(0,2,?), 25, defrightangle2(0,1,2,?)).