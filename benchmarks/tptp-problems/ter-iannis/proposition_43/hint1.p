%% ./larus -vcoq -m8 -l50 benchmarks/tptp-problems/ter-iannis/proposition_43/base.p
% Without -i : 10s to create axioms / 7 to find a solution Size 6

fof(lemma_PGflip,axiom, (! [A,B,C,D] : ((pG(A,B,C,D)) => ((pG(B,A,D,C)))))).
fof(proposition_34,axiom, (! [A,B,C,D] : ((pG(A,C,D,B)) => ((cong(A,B,C,D) & cong(A,C,B,D) & congA(C,A,B,B,D,C) & congA(A,B,D,D,C,A) & cong_3(C,A,B,B,D,C)))))).
fof(axiom_congruentequal,axiom, (! [A,B,C,Ca,Cb,Cc] : ((cong_3(A,B,C,Ca,Cb,Cc)) => ((eT(A,B,C,Ca,Cb,Cc)))))).
fof(axiom_ETpermutation,axiom, (! [A,B,C,Ca,Cb,Cc] : ((eT(A,B,C,Ca,Cb,Cc)) => ((eT(A,B,C,Cb,Cc,Ca) & eT(A,B,C,Ca,Cc,Cb) & eT(A,B,C,Cb,Ca,Cc) & eT(A,B,C,Cc,Cb,Ca) & eT(A,B,C,Cc,Ca,Cb)))))).
fof(axiom_ETsymmetric,axiom, (! [A,B,C,Ca,Cb,Cc] : ((eT(A,B,C,Ca,Cb,Cc)) => ((eT(Ca,Cb,Cc,A,B,C)))))).
fof(axiom_cutoff1,axiom, (! [A,B,C,D,E,Ca,Cb,Cc,Cd,Ce] : ((betS(A,B,C) & betS(Ca,Cb,Cc) & betS(E,D,C) & betS(Ce,Cd,Cc) & eT(B,C,D,Cb,Cc,Cd) & eT(A,C,E,Ca,Cc,Ce)) => ((eF(A,B,D,E,Ca,Cb,Cd,Ce)))))).
fof(axiom_betweennesssymmetry,axiom, (! [A,B,C] : ((betS(A,B,C)) => ((betS(C,B,A)))))).
fof(axiom_EFpermutation,axiom, (! [A,B,C,D,Ca,Cb,Cc,Cd] : ((eF(A,B,C,D,Ca,Cb,Cc,Cd)) => ((eF(A,B,C,D,Cb,Cc,Cd,Ca) & eF(A,B,C,D,Cd,Cc,Cb,Ca) & eF(A,B,C,D,Cc,Cd,Ca,Cb) & eF(A,B,C,D,Cb,Ca,Cd,Cc) & eF(A,B,C,D,Cd,Ca,Cb,Cc) & eF(A,B,C,D,Cc,Cb,Ca,Cd) & eF(A,B,C,D,Ca,Cd,Cc,Cb)))))).
fof(axiom_EFsymmetric,axiom, (! [A,B,C,D,Ca,Cb,Cc,Cd] : ((eF(A,B,C,D,Ca,Cb,Cc,Cd)) => ((eF(Ca,Cb,Cc,Cd,A,B,C,D)))))).
fof(axiom_cutoff2,axiom, (! [A,B,C,D,E,Ca,Cb,Cc,Cd,Ce] : ((betS(B,C,D) & betS(Cb,Cc,Cd) & eT(C,D,E,Cc,Cd,Ce) & eF(A,B,D,E,Ca,Cb,Cd,Ce)) => ((eF(A,B,C,E,Ca,Cb,Cc,Ce)))))).
fof(proposition_43,conjecture,(! [A,B,C,D,E,F,G,H,K] : ((pG(A,B,C,D) & betS(A,H,D) & betS(A,E,B) & betS(D,F,C) & betS(B,G,C) & betS(A,K,C) & pG(E,A,H,K) & pG(G,K,F,C)) => ((eF(K,G,B,E,D,F,K,H)))))).

fof(hintname1, hint, _, _, axiom_EFpermutation(5,3,7,8,6,1,4,1)).
%fof(hintname2, hint, _, _, axiom_EFsymmetric(?,?,?,?,?,?,?,?)).
%fof(hintname3, hint, _, _, axiom_cutoff1(?,?,?,?,?,?,?,?,?,?)).