fof(lemma_parallelsymmetric,axiom, (! [A,B,C,D] : ((par(A,B,C,D)) => ((par(C,D,A,B)))))).
fof(lemma_paralleldef2B,axiom, (! [A,B,C,D] : ((par(A,B,C,D)) => ((tP(A,B,C,D)))))).
fof(deftarski_parallel,axiom, (! [A,B,C,D] : ((tP(A,B,C,D)) => ((neq(A,B) & neq(C,D) & nmeet(A,B,C,D) & oS(C,D,A,B)))))).
fof(deftarski_parallel2,axiom, (! [A,B,C,D] : ((neq(A,B) & neq(C,D) & nmeet(A,B,C,D) & oS(C,D,A,B)) => ((tP(A,B,C,D)))))).
fof(lemma_parallelNC,axiom, (! [A,B,C,D] : ((par(A,B,C,D)) => ((ncol(A,B,C) & ncol(A,C,D) & ncol(B,C,D) & ncol(A,B,D)))))).
fof(lemma_NCdistinct,axiom, (! [A,B,C] : ((ncol(A,B,C)) => ((neq(A,B) & neq(B,C) & neq(A,C) & neq(B,A) & neq(C,B) & neq(C,A)))))).
fof(lemma_extension,axiom, (! [A,B,P,Q] : (? [X] : ((neq(A,B) & neq(P,Q)) => ((betS(A,B,X) & cong(B,X,P,Q))))))).
fof(defcollinear,axiom, (! [A,B,C] : ((col(A,B,C)) => ((eq(A,B)) | (eq(A,C)) | (eq(B,C)) | (betS(B,A,C)) | (betS(A,B,C)) | (betS(A,C,B)))))).
fof(defcollinear2a,axiom, (! [A,B,C] : ((eq(A,B)) => ((col(A,B,C)))))).
fof(defcollinear2b,axiom, (! [A,B,C] : ((eq(A,C)) => ((col(A,B,C)))))).
fof(defcollinear2c,axiom, (! [A,B,C] : ((eq(B,C)) => ((col(A,B,C)))))).
fof(defcollinear2d,axiom, (! [A,B,C] : ((betS(B,A,C)) => ((col(A,B,C)))))).
fof(defcollinear2e,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((col(A,B,C)))))).
fof(defcollinear2f,axiom, (! [A,B,C] : ((betS(A,C,B)) => ((col(A,B,C)))))).
fof(lemma_NCorder,axiom, (! [A,B,C] : ((ncol(A,B,C)) => ((ncol(B,A,C) & ncol(B,C,A) & ncol(C,A,B) & ncol(A,C,B) & ncol(C,B,A)))))).
fof(lemma_samesidesymmetric,axiom, (! [A,B,P,Q] : ((oS(P,Q,A,B)) => ((oS(Q,P,A,B) & oS(P,Q,B,A) & oS(Q,P,B,A)))))).
fof(defoppositeside,axiom, (! [P,A,B,Q] : (? [X] : ((tS(P,A,B,Q)) => ((betS(P,X,Q) & col(A,B,X) & ncol(A,B,P))))))).
fof(defoppositeside2,axiom, (! [P,A,B,Q,X] : ((betS(P,X,Q) & col(A,B,X) & ncol(A,B,P)) => ((tS(P,A,B,Q)))))).
fof(lemma_planeseparation,axiom, (! [A,B,C,D,E] : ((oS(C,D,A,B) & tS(D,A,B,E)) => ((tS(C,A,B,E)))))).
fof(lemma_inequalitysymmetric,axiom, (! [A,B] : ((neq(A,B)) => ((neq(B,A)))))).
fof(lemma_collinearorder,axiom, (! [A,B,C] : ((col(A,B,C)) => ((col(B,A,C) & col(B,C,A) & col(C,A,B) & col(A,C,B) & col(C,B,A)))))).
fof(lemma_betweennotequal,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((neq(B,C) & neq(A,B) & neq(A,C)))))).
fof(lemma_collinear4,axiom, (! [A,B,C,D] : ((col(A,B,C) & col(A,B,D) & neq(A,B)) => ((col(B,C,D)))))).
fof(lemma_NChelper,axiom, (! [A,B,C,P,Q] : ((ncol(A,B,C) & col(A,B,P) & col(A,B,Q) & neq(P,Q)) => ((ncol(P,Q,C)))))).
fof(postulate_Pasch_inner,axiom, (! [A,B,C,P,Q] : (? [X] : ((betS(A,P,C) & betS(B,Q,C) & ncol(A,C,B)) => ((betS(A,X,Q) & betS(B,X,P))))))).
fof(axiom_betweennesssymmetry,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((betS(C,B,A)))))).
fof(defcross,axiom, (! [A,B,C,D] : (? [X] : ((cR(A,B,C,D)) => ((betS(A,X,B) & betS(C,X,D))))))).
fof(defcross2,axiom, (! [A,B,C,D,X] : ((betS(A,X,B) & betS(C,X,D)) => ((cR(A,B,C,D)))))).
fof(postulate_Pasch_outer,axiom, (! [A,B,C,P,Q] : (? [X] : ((betS(A,P,C) & betS(B,C,Q) & ncol(B,Q,A)) => ((betS(A,X,Q) & betS(B,P,X))))))).
fof(lemma_parallelflip,axiom, (! [A,B,C,D] : ((par(A,B,C,D)) => ((par(B,A,C,D) & par(A,B,D,C) & par(B,A,D,C)))))).
fof(defparallel,axiom, (! [A,B,C,D] : (? [U,V,Su,Sv,X] : ((par(A,B,C,D)) => ((neq(A,B) & neq(C,D) & col(A,B,U) & col(A,B,V) & neq(U,V) & col(C,D,Su) & col(C,D,Sv) & neq(Su,Sv) & nmeet(A,B,C,D) & betS(U,X,Sv) & betS(Su,X,V))))))).
fof(defparallel2,axiom, (! [A,B,C,D,U,V,Su,Sv,X] : ((neq(A,B) & neq(C,D) & col(A,B,U) & col(A,B,V) & neq(U,V) & col(C,D,Su) & col(C,D,Sv) & neq(Su,Sv) & nmeet(A,B,C,D) & betS(U,X,Sv) & betS(Su,X,V)) => ((par(A,B,C,D)))))).
fof(lemma_collinearbetween,axiom, (! [A,B,C,D,E,F,H] : ((col(A,E,B) & col(C,F,D) & neq(A,B) & neq(C,D) & neq(A,E) & neq(F,D) & nmeet(A,B,C,D) & betS(A,H,D) & col(E,F,H)) => ((betS(E,H,F)))))).
fof(lemma_3_5b,axiom, (! [A,B,C,D] : ((betS(A,B,D) & betS(B,C,D)) => ((betS(A,C,D)))))).
fof(axiom_innertransitivity,axiom, (! [A,B,C,D] : ((betS(A,B,D) & betS(B,C,D)) => ((betS(A,B,C)))))).
fof(lemma_collinearparallel,axiom, (! [A,B,C,Xc,Xd] : ((par(A,B,Xc,Xd) & col(Xc,Xd,C) & neq(C,Xd)) => ((par(A,B,C,Xd)))))).
fof(lemma_3_6b,axiom, (! [A,B,C,D] : ((betS(A,B,C) & betS(A,C,D)) => ((betS(A,B,D)))))).
fof(eq_excluded_middle,axiom, (! [A,B] : ((eq(A,B)) | (neq(A,B))))).
fof(par_excluded_middle,axiom, (! [A,B,C,D] : ((par(A,B,C,D)) | (npar(A,B,C,D))))).
fof(tP_excluded_middle,axiom, (! [A,B,C,D] : ((tP(A,B,C,D)) | (ntP(A,B,C,D))))).
fof(meet_excluded_middle,axiom, (! [A,B,C,D] : ((meet(A,B,C,D)) | (nmeet(A,B,C,D))))).
fof(oS_excluded_middle,axiom, (! [A,B,C,D] : ((oS(A,B,C,D)) | (noS(A,B,C,D))))).
fof(col_excluded_middle,axiom, (! [A,B,C] : ((col(A,B,C)) | (ncol(A,B,C))))).
fof(betS_excluded_middle,axiom, (! [A,B,C] : ((betS(A,B,C)) | (nbetS(A,B,C))))).
fof(cong_excluded_middle,axiom, (! [A,B,C,D] : ((cong(A,B,C,D)) | (ncong(A,B,C,D))))).
fof(tS_excluded_middle,axiom, (! [A,B,C,D] : ((tS(A,B,C,D)) | (ntS(A,B,C,D))))).
fof(cR_excluded_middle,axiom, (! [A,B,C,D] : ((cR(A,B,C,D)) | (ncR(A,B,C,D))))).
fof(lemma_crisscross,conjecture,(  ! [A,B,C,D] : ((par(A,C,B,D) & ncR(A,B,C,D)) => (cR(A,D,B,C))))).