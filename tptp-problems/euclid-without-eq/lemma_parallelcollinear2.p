fof(deftarski_parallel,axiom, (! [A,B,C,D] : ((tP(A,B,C,D)) => ((neq(A,B) & neq(C,D) & nmeet(A,B,C,D) & oS(C,D,A,B)))))).
fof(deftarski_parallel2,axiom, (! [A,B,C,D] : ((neq(A,B) & neq(C,D) & nmeet(A,B,C,D) & oS(C,D,A,B)) => ((tP(A,B,C,D)))))).
fof(defsameside,axiom, (! [P,Q,A,B] : (? [X,U,V] : ((oS(P,Q,A,B)) => ((col(A,B,U) & col(A,B,V) & betS(P,U,X) & betS(Q,V,X) & ncol(A,B,P) & ncol(A,B,Q))))))).
fof(defsameside2,axiom, (! [P,Q,A,B,X,U,V] : ((col(A,B,U) & col(A,B,V) & betS(P,U,X) & betS(Q,V,X) & ncol(A,B,P) & ncol(A,B,Q)) => ((oS(P,Q,A,B)))))).
fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((neq(B,C) & neq(A,B) & neq(A,C)))))).
fof(axiom_betweennesssymmetry,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((betS(C,B,A)))))).
fof(defcollinear,axiom, (! [A,B,C] : ((col(A,B,C)) => ((eq(A,B)) | (eq(A,C)) | (eq(B,C)) | (betS(B,A,C)) | (betS(A,B,C)) | (betS(A,C,B)))))).
fof(defcollinear2a,axiom, (! [A,B,C] : ((eq(A,B)) => ((col(A,B,C)))))).
fof(defcollinear2b,axiom, (! [A,B,C] : ((eq(A,C)) => ((col(A,B,C)))))).
fof(defcollinear2c,axiom, (! [A,B,C] : ((eq(B,C)) => ((col(A,B,C)))))).
fof(defcollinear2d,axiom, (! [A,B,C] : ((betS(B,A,C)) => ((col(A,B,C)))))).
fof(defcollinear2e,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((col(A,B,C)))))).
fof(defcollinear2f,axiom, (! [A,B,C] : ((betS(A,C,B)) => ((col(A,B,C)))))).
fof(lemma_collinear4,axiom, (! [A,B,C,D] : ((col(A,B,C) & col(A,B,D) & neq(A,B)) => ((col(B,C,D)))))).
fof(lemma_collinearorder,axiom, (! [A,B,C] : ((col(A,B,C)) => ((col(B,A,C) & col(B,C,A) & col(C,A,B) & col(A,C,B) & col(C,B,A)))))).
fof(defmeet,axiom, (! [A,B,C,D] : (? [X] : ((meet(A,B,C,D)) => ((neq(A,B) & neq(C,D) & col(A,B,X) & col(C,D,X))))))).
fof(defmeet2,axiom, (! [A,B,C,D,X] : ((neq(A,B) & neq(C,D) & col(A,B,X) & col(C,D,X)) => ((meet(A,B,C,D)))))).
fof(lemma_NChelper,axiom, (! [A,B,C,P,Q] : ((ncol(A,B,C) & col(A,B,P) & col(A,B,Q) & neq(P,Q)) => ((ncol(P,Q,C)))))).
fof(lemma_NCorder,axiom, (! [A,B,C] : ((ncol(A,B,C)) => ((ncol(B,A,C) & ncol(B,C,A) & ncol(C,A,B) & ncol(A,C,B) & ncol(C,B,A)))))).
fof(postulate_Pasch_inner,axiom, (! [A,B,C,P,Q] : (? [X] : ((betS(A,P,C) & betS(B,Q,C) & ncol(A,C,B)) => ((betS(A,X,Q) & betS(B,X,P))))))).
fof(lemma_inequalitysymmetric,axiom, (! [A,B] : ((neq(A,B)) => ((neq(B,A)))))).
fof(lemma_3_6b,axiom, (! [A,B,C,D] : ((betS(A,B,C) & betS(A,C,D)) => ((betS(A,B,D)))))).
fof(lemma_collinear5,axiom, (! [A,B,C,D,E] : ((neq(A,B) & col(A,B,C) & col(A,B,D) & col(A,B,E)) => ((col(C,D,E)))))).
fof(eq_excluded_middle,axiom, (! [A,B] : ((eq(A,B)) | (neq(A,B))))).
fof(tP_excluded_middle,axiom, (! [A,B,C,D] : ((tP(A,B,C,D)) | (ntP(A,B,C,D))))).
fof(meet_excluded_middle,axiom, (! [A,B,C,D] : ((meet(A,B,C,D)) | (nmeet(A,B,C,D))))).
fof(oS_excluded_middle,axiom, (! [A,B,C,D] : ((oS(A,B,C,D)) | (noS(A,B,C,D))))).
fof(col_excluded_middle,axiom, (! [A,B,C] : ((col(A,B,C)) | (ncol(A,B,C))))).
fof(betS_excluded_middle,axiom, (! [A,B,C] : ((betS(A,B,C)) | (nbetS(A,B,C))))).
fof(lemma_parallelcollinear2,conjecture,(  ! [A,B,C,Xc,Xd] : ((tP(A,B,Xc,Xd) & betS(Xc,C,Xd)) => (tP(A,B,C,Xd))))).