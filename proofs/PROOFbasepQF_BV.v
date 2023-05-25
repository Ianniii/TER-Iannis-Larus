Require Import src.general_tactics.
Require Import Classical.

Section Sec.

Parameter MyT : Type.
Parameter pG : MyT -> MyT -> MyT -> MyT -> Prop.
Parameter cong : MyT -> MyT -> MyT -> MyT -> Prop.
Parameter congA : MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter cong_3 : MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter eT : MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter betS : MyT -> MyT -> MyT -> Prop.
Parameter eF : MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> Prop.

Hypothesis lemma_PGflip : forall A B C D : MyT, pG A B C D -> pG B A D C.
Hypothesis proposition_34 : forall A B C D : MyT, pG A C D B -> cong A B C D /\ cong A C B D /\ congA C A B B D C /\ congA A B D D C A /\ cong_3 C A B B D C.
Hypothesis axiom_congruentequal : forall A B C Ca Cb Cc : MyT, cong_3 A B C Ca Cb Cc -> eT A B C Ca Cb Cc.
Hypothesis axiom_ETpermutation : forall A B C Ca Cb Cc : MyT, eT A B C Ca Cb Cc -> eT A B C Cb Cc Ca /\ eT A B C Ca Cc Cb /\ eT A B C Cb Ca Cc /\ eT A B C Cc Cb Ca /\ eT A B C Cc Ca Cb.
Hypothesis axiom_ETsymmetric : forall A B C Ca Cb Cc : MyT, eT A B C Ca Cb Cc -> eT Ca Cb Cc A B C.
Hypothesis axiom_cutoff1 : forall A B C D E Ca Cb Cc Cd Ce : MyT, betS A B C -> betS Ca Cb Cc -> betS E D C -> betS Ce Cd Cc -> eT B C D Cb Cc Cd -> eT A C E Ca Cc Ce -> eF A B D E Ca Cb Cd Ce.
Hypothesis axiom_betweennesssymmetry : forall A B C : MyT, betS A B C -> betS C B A.
Hypothesis axiom_EFpermutation : forall A B C D Ca Cb Cc Cd : MyT, eF A B C D Ca Cb Cc Cd -> eF A B C D Cb Cc Cd Ca /\ eF A B C D Cd Cc Cb Ca /\ eF A B C D Cc Cd Ca Cb /\ eF A B C D Cb Ca Cd Cc /\ eF A B C D Cd Ca Cb Cc /\ eF A B C D Cc Cb Ca Cd /\ eF A B C D Ca Cd Cc Cb.
Hypothesis axiom_EFsymmetric : forall A B C D Ca Cb Cc Cd : MyT, eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd A B C D.
Hypothesis axiom_cutoff2 : forall A B C D E Ca Cb Cc Cd Ce : MyT, betS B C D -> betS Cb Cc Cd -> eT C D E Cc Cd Ce -> eF A B D E Ca Cb Cd Ce -> eF A B C E Ca Cb Cc Ce.

Lemma lemma_PGflipsat0 : forall  A  B  C  D,  pG A B C D -> cong_3 A B C C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0 : Sym.

Lemma lemma_PGflipsat1 : forall  A  B  C  D,  pG A B C D -> congA B C D D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat1 : Sym.

Lemma lemma_PGflipsat2 : forall  A  B  C  D,  pG A B C D -> congA A B C C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat2 : Sym.

Lemma lemma_PGflipsat3 : forall  A  B  C  D,  pG A B C D -> cong B A C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat3 : Sym.

Lemma lemma_PGflipsat4 : forall  A  B  C  D,  pG A B C D -> cong B C A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat4 : Sym.

Lemma proposition_34AuxConjConcl8sat5 : forall  A  B  C  D,  pG A C D B -> eT C A B B D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5 : Sym.

Lemma lemma_PGflipsat0sat6 : forall  A  B  C  D,  pG A B C D -> eT A B C C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6 : Sym.

Lemma axiom_congruentequalsat7 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A B C Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7 : Sym.

Lemma axiom_ETsymmetricsat8 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cb Cc C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9 : forall  A  B  C  D,  pG A C D B -> eT C A B C B D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9 : Sym.

Lemma lemma_PGflipsat0sat6sat10 : forall  A  B  C  D,  pG A B C D -> eT A B C A C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10 : Sym.

Lemma axiom_congruentequalsat7sat11 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A B C Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11 : Sym.

Lemma axiom_ETsymmetricsat8sat12 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cb Cc B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13 : forall  A  B  C  D,  pG A C D B -> eT C A B D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14 : forall  A  B  C  D,  pG A B C D -> eT A B C D A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14 : Sym.

Lemma axiom_congruentequalsat15 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A B C Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15 : Sym.

Lemma axiom_ETsymmetricsat16 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cb Cc C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17 : forall  A  B  C  D,  pG A C D B -> eT C A B C D B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17 : Sym.

Lemma lemma_PGflipsat0sat6sat18 : forall  A  B  C  D,  pG A B C D -> eT A B C A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18 : Sym.

Lemma axiom_congruentequalsat7sat19 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A B C Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19 : Sym.

Lemma axiom_ETsymmetricsat8sat20 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cb Cc B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21 : forall  A  B  C  D,  pG A C D B -> eT C A B D B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22 : forall  A  B  C  D,  pG A B C D -> eT A B C D C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22 : Sym.

Lemma axiom_congruentequalsat7sat11sat23 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A B C Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cb Cc A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25 : forall  A  B  C  D,  pG A C D B -> eT C A B B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26 : forall  A  B  C  D,  pG A B C D -> eT A B C C A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26 : Sym.

Lemma axiom_congruentequalsat27 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cb Cc A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat27 : Sym.

Lemma axiom_ETpermutationAuxConjConcl8sat28 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Ca Cb A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl8sat28 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat29 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Cb Ca A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat29 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat30 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Ca Cc A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat30 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat31 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cc Cb A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat31 : Sym.

Lemma axiom_ETpermutationAuxConjConcl0sat32 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Cc Ca A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl0sat32 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat33 : forall  A  B  C  D,  pG A C D B -> eT B D C C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat33 : Sym.

Lemma lemma_PGflipsat0sat6sat34 : forall  A  B  C  D,  pG A B C D -> eT C D A A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat34 : Sym.

Lemma axiom_congruentequalsat7sat35 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Ca Cb A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat35 : Sym.

Lemma axiom_ETsymmetricsat8sat36 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C A B Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat36 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat37 : forall  A  B  C  D,  pG A C D B -> eT C B D C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat37 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat38 : forall  A  B  C  D,  pG A B C D -> eT A C D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat38 : Sym.

Lemma axiom_congruentequalsat7sat11sat39 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Cc Ca A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat39 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat40 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B C A Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat40 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat41 : forall  A  B  C  D,  pG A C D B -> eT D C B C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat41 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat42 : forall  A  B  C  D,  pG A B C D -> eT D A C A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat42 : Sym.

Lemma axiom_congruentequalsat15sat43 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Cb Ca A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat43 : Sym.

Lemma axiom_ETsymmetricsat16sat44 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C B A Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat44 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat45 : forall  A  B  C  D,  pG A C D B -> eT C D B C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat45 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat46 : forall  A  B  C  D,  pG A B C D -> eT A D C A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat46 : Sym.

Lemma axiom_congruentequalsat7sat19sat47 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Ca Cc A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat47 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat48 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B A C Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat48 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat49 : forall  A  B  C  D,  pG A C D B -> eT D B C C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat49 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat50 : forall  A  B  C  D,  pG A B C D -> eT D C A A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat50 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat51 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cc Cb A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat51 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat52 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT A C B Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat52 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat53 : forall  A  B  C  D,  pG A C D B -> eT B C D C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat53 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat54 : forall  A  B  C  D,  pG A B C D -> eT C A D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat54 : Sym.

Lemma axiom_EFsymmetricsat55 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55 : Sym.

Lemma axiom_EFsymmetricsat56 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56 : Sym.

Lemma axiom_EFsymmetricsat55sat57 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57 : Sym.

Lemma axiom_EFsymmetricsat58 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58 : Sym.

Lemma axiom_EFsymmetricsat55sat59 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59 : Sym.

Lemma axiom_EFsymmetricsat56sat60 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cb Cc Cd B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61 : Sym.

Lemma axiom_EFpermutationAuxConjConcl12sat62 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl12sat62 : Sym.

Lemma axiom_EFpermutationAuxConjConcl10sat63 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl10sat63 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat64 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat64 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat65 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat65 : Sym.

Lemma axiom_EFpermutationAuxConjConcl4sat66 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl4sat66 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat67 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat67 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat68 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat68 : Sym.

Lemma axiom_EFsymmetricsat55sat69 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Ca Cb Cc Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat69 : Sym.

Lemma axiom_EFsymmetricsat56sat70 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Ca Cb Cc Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat70 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat71 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Ca Cb Cc Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat71 : Sym.

Lemma axiom_EFsymmetricsat58sat72 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Ca Cb Cc Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat72 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat73 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Ca Cb Cc Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat73 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat74 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Ca Cb Cc Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat74 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat75 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Ca Cb Cc Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat75 : Sym.

Lemma axiom_congruentequalsat76 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cb Cc C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76 : Sym.

Lemma axiom_ETpermutationAuxConjConcl8sat77 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Ca Cb C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl8sat77 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat78 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Cb Ca C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat78 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat79 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Ca Cc C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat79 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat80 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cc Cb C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat80 : Sym.

Lemma axiom_ETpermutationAuxConjConcl0sat81 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Cc Ca C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl0sat81 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82 : forall  A  B  C  D,  pG A C D B -> eT B D C B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82 : Sym.

Lemma lemma_PGflipsat0sat6sat83 : forall  A  B  C  D,  pG A B C D -> eT C D A C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83 : Sym.

Lemma axiom_congruentequalsat7sat84 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Ca Cb C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84 : Sym.

Lemma axiom_ETsymmetricsat8sat85 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C A B Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat85 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86 : forall  A  B  C  D,  pG A C D B -> eT C B D B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87 : forall  A  B  C  D,  pG A B C D -> eT A C D C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87 : Sym.

Lemma axiom_congruentequalsat7sat11sat88 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Cc Ca C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat89 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B C A Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat89 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90 : forall  A  B  C  D,  pG A C D B -> eT D C B B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91 : forall  A  B  C  D,  pG A B C D -> eT D A C C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91 : Sym.

Lemma axiom_congruentequalsat15sat92 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Cb Ca C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92 : Sym.

Lemma axiom_ETsymmetricsat16sat93 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C B A Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat93 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94 : forall  A  B  C  D,  pG A C D B -> eT C D B B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95 : forall  A  B  C  D,  pG A B C D -> eT A D C C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95 : Sym.

Lemma axiom_congruentequalsat7sat19sat96 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Ca Cc C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat97 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B A C Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat97 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98 : forall  A  B  C  D,  pG A C D B -> eT D B C B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99 : forall  A  B  C  D,  pG A B C D -> eT D C A C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cc Cb C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat101 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT A C B Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat101 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102 : forall  A  B  C  D,  pG A C D B -> eT B C D B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103 : forall  A  B  C  D,  pG A B C D -> eT C A D C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103 : Sym.

Lemma axiom_congruentequalsat76sat104 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C A B Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76sat104 : Sym.

Lemma axiom_ETpermutationAuxConjConcl8sat77sat105 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C A B Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl8sat77sat105 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat78sat106 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C A B Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat78sat106 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat79sat107 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C A B Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat79sat107 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat80sat108 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C A B Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat80sat108 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82sat109 : forall  A  B  C  D,  pG A C D B -> eT B C A C B D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82sat109 : Sym.

Lemma lemma_PGflipsat0sat6sat83sat110 : forall  A  B  C  D,  pG A B C D -> eT C A B A C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83sat110 : Sym.

Lemma axiom_congruentequalsat7sat84sat111 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C A B Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84sat111 : Sym.

Lemma axiom_ETsymmetricsat8sat85sat112 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Ca Cb B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat85sat112 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86sat113 : forall  A  B  C  D,  pG A C D B -> eT B C A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86sat113 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87sat114 : forall  A  B  C  D,  pG A B C D -> eT C A B D A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87sat114 : Sym.

Lemma axiom_congruentequalsat7sat11sat88sat115 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C A B Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88sat115 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90sat116 : forall  A  B  C  D,  pG A C D B -> eT B C A B D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90sat116 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91sat117 : forall  A  B  C  D,  pG A B C D -> eT C A B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91sat117 : Sym.

Lemma axiom_congruentequalsat15sat92sat118 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C A B Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92sat118 : Sym.

Lemma axiom_ETsymmetricsat16sat93sat119 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Ca Cb A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat93sat119 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94sat120 : forall  A  B  C  D,  pG A C D B -> eT B C A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94sat120 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95sat121 : forall  A  B  C  D,  pG A B C D -> eT C A B C A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95sat121 : Sym.

Lemma axiom_congruentequalsat7sat19sat96sat122 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C A B Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96sat122 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat97sat123 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Ca Cb C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat97sat123 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98sat124 : forall  A  B  C  D,  pG A C D B -> eT B C A C D B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98sat124 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99sat125 : forall  A  B  C  D,  pG A B C D -> eT C A B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99sat125 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100sat126 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C A B Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100sat126 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat101sat127 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Ca Cb B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat101sat127 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128 : forall  A  B  C  D,  pG A C D B -> eT B C A D B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103sat129 : forall  A  B  C  D,  pG A B C D -> eT C A B D C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103sat129 : Sym.

Lemma axiom_congruentequalsat76sat104sat130 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Ca Cb B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76sat104sat130 : Sym.

Lemma axiom_ETpermutationAuxConjConcl8sat77sat105sat131 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Cc Ca B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl8sat77sat105sat131 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat78sat106sat132 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cc Cb B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat78sat106sat132 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat79sat107sat133 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Cb Ca B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat79sat107sat133 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat80sat108sat134 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Ca Cc B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat80sat108sat134 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82sat109sat135 : forall  A  B  C  D,  pG A C D B -> eT C B D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82sat109sat135 : Sym.

Lemma lemma_PGflipsat0sat6sat83sat110sat136 : forall  A  B  C  D,  pG A B C D -> eT A C D B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83sat110sat136 : Sym.

Lemma axiom_congruentequalsat7sat84sat111sat137 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Cc Ca B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84sat111sat137 : Sym.

Lemma axiom_ETsymmetricsat8sat85sat112sat138 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B C A Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat85sat112sat138 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86sat113sat139 : forall  A  B  C  D,  pG A C D B -> eT D C B A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86sat113sat139 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87sat114sat140 : forall  A  B  C  D,  pG A B C D -> eT D A C B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87sat114sat140 : Sym.

Lemma axiom_congruentequalsat7sat11sat88sat115sat141 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cb Cc B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88sat115sat141 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142 : forall  A  B  C  D,  pG A C D B -> eT B D C A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91sat117sat143 : forall  A  B  C  D,  pG A B C D -> eT C D A B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91sat117sat143 : Sym.

Lemma axiom_congruentequalsat15sat92sat118sat144 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cc Cb B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92sat118sat144 : Sym.

Lemma axiom_ETsymmetricsat16sat93sat119sat145 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT A C B Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat93sat119sat145 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94sat120sat146 : forall  A  B  C  D,  pG A C D B -> eT B C D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94sat120sat146 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95sat121sat147 : forall  A  B  C  D,  pG A B C D -> eT C A D B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95sat121sat147 : Sym.

Lemma axiom_congruentequalsat7sat19sat96sat122sat148 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Cb Ca B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96sat122sat148 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat97sat123sat149 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C B A Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat97sat123sat149 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150 : forall  A  B  C  D,  pG A C D B -> eT C D B A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99sat125sat151 : forall  A  B  C  D,  pG A B C D -> eT A D C B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99sat125sat151 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100sat126sat152 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Ca Cc B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100sat126sat152 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat101sat127sat153 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B A C Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat101sat127sat153 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154 : forall  A  B  C  D,  pG A C D B -> eT D B C A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155 : forall  A  B  C  D,  pG A B C D -> eT D C A B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155 : Sym.

Lemma axiom_congruentequalsat76sat104sat130sat156 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B C A Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76sat104sat130sat156 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat78sat106sat132sat157 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B C A Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat78sat106sat132sat157 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat79sat107sat133sat158 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B C A Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat79sat107sat133sat158 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat80sat108sat134sat159 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B C A Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat80sat108sat134sat159 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82sat109sat135sat160 : forall  A  B  C  D,  pG A C D B -> eT A B C D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82sat109sat135sat160 : Sym.

Lemma lemma_PGflipsat0sat6sat83sat110sat136sat161 : forall  A  B  C  D,  pG A B C D -> eT B C A D A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83sat110sat136sat161 : Sym.

Lemma axiom_congruentequalsat7sat84sat111sat137sat162 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B C A Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84sat111sat137sat162 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86sat113sat139sat163 : forall  A  B  C  D,  pG A C D B -> eT A B C B D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86sat113sat139sat163 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87sat114sat140sat164 : forall  A  B  C  D,  pG A B C D -> eT B C A C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87sat114sat140sat164 : Sym.

Lemma axiom_congruentequalsat7sat11sat88sat115sat141sat165 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B C A Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88sat115sat141sat165 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142sat166 : forall  A  B  C  D,  pG A C D B -> eT A B C C B D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142sat166 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91sat117sat143sat167 : forall  A  B  C  D,  pG A B C D -> eT B C A A C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91sat117sat143sat167 : Sym.

Lemma axiom_congruentequalsat15sat92sat118sat144sat168 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B C A Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92sat118sat144sat168 : Sym.

Lemma axiom_ETsymmetricsat16sat93sat119sat145sat169 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Cc Ca B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat93sat119sat145sat169 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94sat120sat146sat170 : forall  A  B  C  D,  pG A C D B -> eT A B C D B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94sat120sat146sat170 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95sat121sat147sat171 : forall  A  B  C  D,  pG A B C D -> eT B C A D C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95sat121sat147sat171 : Sym.

Lemma axiom_congruentequalsat7sat19sat96sat122sat148sat172 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B C A Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96sat122sat148sat172 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat97sat123sat149sat173 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Cc Ca A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat97sat123sat149sat173 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150sat174 : forall  A  B  C  D,  pG A C D B -> eT A B C B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150sat174 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99sat125sat151sat175 : forall  A  B  C  D,  pG A B C D -> eT B C A C A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99sat125sat151sat175 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100sat126sat152sat176 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B C A Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100sat126sat152sat176 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat101sat127sat153sat177 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Cc Ca C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat101sat127sat153sat177 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154sat178 : forall  A  B  C  D,  pG A C D B -> eT A B C C D B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154sat178 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155sat179 : forall  A  B  C  D,  pG A B C D -> eT B C A A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155sat179 : Sym.

Lemma axiom_congruentequalsat180 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cb Cc C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat180 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat181 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Cb Ca C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat181 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat182 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Ca Cc C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat182 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat183 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cc Cb C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat183 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat184 : forall  A  B  C  D,  pG A C D B -> eT B D C B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat184 : Sym.

Lemma lemma_PGflipsat0sat6sat185 : forall  A  B  C  D,  pG A B C D -> eT C D A C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat185 : Sym.

Lemma axiom_congruentequalsat7sat186 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Ca Cb C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat186 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat187 : forall  A  B  C  D,  pG A C D B -> eT C B D B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat187 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat188 : forall  A  B  C  D,  pG A B C D -> eT A C D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat188 : Sym.

Lemma axiom_congruentequalsat7sat11sat189 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Cc Ca C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat189 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat190 : forall  A  B  C  D,  pG A C D B -> eT D C B B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat190 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat191 : forall  A  B  C  D,  pG A B C D -> eT D A C C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat191 : Sym.

Lemma axiom_congruentequalsat15sat192 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Cb Ca C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat192 : Sym.

Lemma axiom_ETsymmetricsat16sat193 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C B A Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat193 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat194 : forall  A  B  C  D,  pG A C D B -> eT C D B B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat194 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat195 : forall  A  B  C  D,  pG A B C D -> eT A D C C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat195 : Sym.

Lemma axiom_congruentequalsat7sat19sat196 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Ca Cc C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat196 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat197 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B A C Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat197 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat198 : forall  A  B  C  D,  pG A C D B -> eT D B C B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat198 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat199 : forall  A  B  C  D,  pG A B C D -> eT D C A C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat199 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat200 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cc Cb C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat200 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat201 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT A C B Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat201 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat202 : forall  A  B  C  D,  pG A C D B -> eT B C D B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat202 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat203 : forall  A  B  C  D,  pG A B C D -> eT C A D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat203 : Sym.

Lemma axiom_congruentequalsat76sat104sat204 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Ca Cb B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76sat104sat204 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat78sat106sat205 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cc Cb B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat78sat106sat205 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat79sat107sat206 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Cb Ca B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat79sat107sat206 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat80sat108sat207 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Ca Cc B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat80sat108sat207 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82sat109sat208 : forall  A  B  C  D,  pG A C D B -> eT C B D A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82sat109sat208 : Sym.

Lemma lemma_PGflipsat0sat6sat83sat110sat209 : forall  A  B  C  D,  pG A B C D -> eT A C D B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83sat110sat209 : Sym.

Lemma axiom_congruentequalsat7sat84sat111sat210 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Cc Ca B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84sat111sat210 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86sat113sat211 : forall  A  B  C  D,  pG A C D B -> eT D C B A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86sat113sat211 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87sat114sat212 : forall  A  B  C  D,  pG A B C D -> eT D A C B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87sat114sat212 : Sym.

Lemma axiom_congruentequalsat7sat11sat88sat115sat213 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cb Cc B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88sat115sat213 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat214 : forall  A  B  C  D,  pG A C D B -> eT B D C A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat214 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91sat117sat215 : forall  A  B  C  D,  pG A B C D -> eT C D A B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91sat117sat215 : Sym.

Lemma axiom_congruentequalsat15sat92sat118sat216 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cc Cb B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92sat118sat216 : Sym.

Lemma axiom_ETsymmetricsat16sat93sat119sat217 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT A C B Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat93sat119sat217 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94sat120sat218 : forall  A  B  C  D,  pG A C D B -> eT B C D A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94sat120sat218 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95sat121sat219 : forall  A  B  C  D,  pG A B C D -> eT C A D B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95sat121sat219 : Sym.

Lemma axiom_congruentequalsat7sat19sat96sat122sat220 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Cb Ca B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96sat122sat220 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat97sat123sat221 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C B A Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat97sat123sat221 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat222 : forall  A  B  C  D,  pG A C D B -> eT C D B A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat222 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99sat125sat223 : forall  A  B  C  D,  pG A B C D -> eT A D C B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99sat125sat223 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100sat126sat224 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Ca Cc B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100sat126sat224 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat101sat127sat225 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B A C Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat101sat127sat225 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat226 : forall  A  B  C  D,  pG A C D B -> eT D B C A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat226 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat227 : forall  A  B  C  D,  pG A B C D -> eT D C A B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat227 : Sym.

Lemma axiom_congruentequalsat76sat104sat130sat156sat228 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Cc Ca A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76sat104sat130sat156sat228 : Sym.

Lemma axiom_ETpermutationAuxConjConcl6sat78sat106sat132sat157sat229 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cb Ca Cc A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl6sat78sat106sat132sat157sat229 : Sym.

Lemma axiom_ETpermutationAuxConjConcl4sat79sat107sat133sat158sat230 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Ca Cc Cb A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl4sat79sat107sat133sat158sat230 : Sym.

Lemma axiom_ETpermutationAuxConjConcl2sat80sat108sat134sat159sat231 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT Cc Cb Ca A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETpermutationAuxConjConcl2sat80sat108sat134sat159sat231 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82sat109sat135sat160sat232 : forall  A  B  C  D,  pG A C D B -> eT D C B C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82sat109sat135sat160sat232 : Sym.

Lemma lemma_PGflipsat0sat6sat83sat110sat136sat161sat233 : forall  A  B  C  D,  pG A B C D -> eT D A C A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83sat110sat136sat161sat233 : Sym.

Lemma axiom_congruentequalsat7sat84sat111sat137sat162sat234 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cb Cc A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84sat111sat137sat162sat234 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86sat113sat139sat163sat235 : forall  A  B  C  D,  pG A C D B -> eT B D C C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86sat113sat139sat163sat235 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87sat114sat140sat164sat236 : forall  A  B  C  D,  pG A B C D -> eT C D A A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87sat114sat140sat164sat236 : Sym.

Lemma axiom_congruentequalsat7sat11sat88sat115sat141sat165sat237 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Ca Cb A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88sat115sat141sat165sat237 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142sat166sat238 : forall  A  B  C  D,  pG A C D B -> eT C B D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142sat166sat238 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91sat117sat143sat167sat239 : forall  A  B  C  D,  pG A B C D -> eT A C D A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91sat117sat143sat167sat239 : Sym.

Lemma axiom_congruentequalsat15sat92sat118sat144sat168sat240 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cb Ca Cc A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92sat118sat144sat168sat240 : Sym.

Lemma axiom_ETsymmetricsat16sat93sat119sat145sat169sat241 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT B A C Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat16sat93sat119sat145sat169sat241 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94sat120sat146sat170sat242 : forall  A  B  C  D,  pG A C D B -> eT D B C C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94sat120sat146sat170sat242 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95sat121sat147sat171sat243 : forall  A  B  C  D,  pG A B C D -> eT D C A A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95sat121sat147sat171sat243 : Sym.

Lemma axiom_congruentequalsat7sat19sat96sat122sat148sat172sat244 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Ca Cc Cb A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96sat122sat148sat172sat244 : Sym.

Lemma axiom_ETsymmetricsat8sat20sat97sat123sat149sat173sat245 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT A C B Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat20sat97sat123sat149sat173sat245 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150sat174sat246 : forall  A  B  C  D,  pG A C D B -> eT B C D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150sat174sat246 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99sat125sat151sat175sat247 : forall  A  B  C  D,  pG A B C D -> eT C A D A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99sat125sat151sat175sat247 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100sat126sat152sat176sat248 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT Cc Cb Ca A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100sat126sat152sat176sat248 : Sym.

Lemma axiom_ETsymmetricsat8sat12sat24sat101sat127sat153sat177sat249 : forall  A  B  C  Ca  Cb  Cc,  eT A B C Ca Cb Cc -> eT C B A Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_ETsymmetricsat8sat12sat24sat101sat127sat153sat177sat249 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154sat178sat250 : forall  A  B  C  D,  pG A C D B -> eT C D B C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154sat178sat250 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155sat179sat251 : forall  A  B  C  D,  pG A B C D -> eT A D C A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155sat179sat251 : Sym.

Lemma axiom_congruentequalsat180sat252 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C B A Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat180sat252 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat184sat253 : forall  A  B  C  D,  pG A C D B -> eT B A C C D B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat184sat253 : Sym.

Lemma lemma_PGflipsat0sat6sat185sat254 : forall  A  B  C  D,  pG A B C D -> eT C B A A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat185sat254 : Sym.

Lemma axiom_congruentequalsat7sat186sat255 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C B A Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat186sat255 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat187sat256 : forall  A  B  C  D,  pG A C D B -> eT B A C D B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat187sat256 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat188sat257 : forall  A  B  C  D,  pG A B C D -> eT C B A D C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat188sat257 : Sym.

Lemma axiom_congruentequalsat7sat11sat189sat258 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C B A Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat189sat258 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat190sat259 : forall  A  B  C  D,  pG A C D B -> eT B A C B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat190sat259 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat191sat260 : forall  A  B  C  D,  pG A B C D -> eT C B A C A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat191sat260 : Sym.

Lemma axiom_congruentequalsat15sat192sat261 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C B A Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat192sat261 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat194sat262 : forall  A  B  C  D,  pG A C D B -> eT B A C B D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat194sat262 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat195sat263 : forall  A  B  C  D,  pG A B C D -> eT C B A C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat195sat263 : Sym.

Lemma axiom_congruentequalsat7sat19sat196sat264 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C B A Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat196sat264 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat198sat265 : forall  A  B  C  D,  pG A C D B -> eT B A C C B D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat198sat265 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat199sat266 : forall  A  B  C  D,  pG A B C D -> eT C B A A C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat199sat266 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat200sat267 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT C B A Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat200sat267 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat202sat268 : forall  A  B  C  D,  pG A C D B -> eT B A C D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat202sat268 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat203sat269 : forall  A  B  C  D,  pG A B C D -> eT C B A D A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat203sat269 : Sym.

Lemma axiom_congruentequalsat76sat104sat204sat270 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B A C Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76sat104sat204sat270 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82sat109sat208sat271 : forall  A  B  C  D,  pG A C D B -> eT A C B D B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82sat109sat208sat271 : Sym.

Lemma lemma_PGflipsat0sat6sat83sat110sat209sat272 : forall  A  B  C  D,  pG A B C D -> eT B A C D C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83sat110sat209sat272 : Sym.

Lemma axiom_congruentequalsat7sat84sat111sat210sat273 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B A C Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84sat111sat210sat273 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86sat113sat211sat274 : forall  A  B  C  D,  pG A C D B -> eT A C B B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86sat113sat211sat274 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87sat114sat212sat275 : forall  A  B  C  D,  pG A B C D -> eT B A C C A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87sat114sat212sat275 : Sym.

Lemma axiom_congruentequalsat7sat11sat88sat115sat213sat276 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B A C Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88sat115sat213sat276 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat214sat277 : forall  A  B  C  D,  pG A C D B -> eT A C B C D B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat214sat277 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91sat117sat215sat278 : forall  A  B  C  D,  pG A B C D -> eT B A C A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91sat117sat215sat278 : Sym.

Lemma axiom_congruentequalsat15sat92sat118sat216sat279 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B A C Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92sat118sat216sat279 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94sat120sat218sat280 : forall  A  B  C  D,  pG A C D B -> eT A C B D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94sat120sat218sat280 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95sat121sat219sat281 : forall  A  B  C  D,  pG A B C D -> eT B A C D A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95sat121sat219sat281 : Sym.

Lemma axiom_congruentequalsat7sat19sat96sat122sat220sat282 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B A C Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96sat122sat220sat282 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat222sat283 : forall  A  B  C  D,  pG A C D B -> eT A C B B D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat222sat283 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99sat125sat223sat284 : forall  A  B  C  D,  pG A B C D -> eT B A C C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99sat125sat223sat284 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100sat126sat224sat285 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT B A C Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100sat126sat224sat285 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat226sat286 : forall  A  B  C  D,  pG A C D B -> eT A C B C B D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat226sat286 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat227sat287 : forall  A  B  C  D,  pG A B C D -> eT B A C A C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat227sat287 : Sym.

Lemma axiom_congruentequalsat76sat104sat130sat156sat228sat288 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A C B Ca Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat76sat104sat130sat156sat228sat288 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat82sat109sat135sat160sat232sat289 : forall  A  B  C  D,  pG A C D B -> eT C B A B C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat82sat109sat135sat160sat232sat289 : Sym.

Lemma lemma_PGflipsat0sat6sat83sat110sat136sat161sat233sat290 : forall  A  B  C  D,  pG A B C D -> eT A C B C A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat83sat110sat136sat161sat233sat290 : Sym.

Lemma axiom_congruentequalsat7sat84sat111sat137sat162sat234sat291 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A C B Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat84sat111sat137sat162sat234sat291 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat86sat113sat139sat163sat235sat292 : forall  A  B  C  D,  pG A C D B -> eT C B A C D B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat86sat113sat139sat163sat235sat292 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat87sat114sat140sat164sat236sat293 : forall  A  B  C  D,  pG A B C D -> eT A C B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat87sat114sat140sat164sat236sat293 : Sym.

Lemma axiom_congruentequalsat7sat11sat88sat115sat141sat165sat237sat294 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A C B Cb Ca Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat88sat115sat141sat165sat237sat294 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142sat166sat238sat295 : forall  A  B  C  D,  pG A C D B -> eT C B A D B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat90sat116sat142sat166sat238sat295 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat91sat117sat143sat167sat239sat296 : forall  A  B  C  D,  pG A B C D -> eT A C B D C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat91sat117sat143sat167sat239sat296 : Sym.

Lemma axiom_congruentequalsat15sat92sat118sat144sat168sat240sat297 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A C B Cc Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat15sat92sat118sat144sat168sat240sat297 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat17sat94sat120sat146sat170sat242sat298 : forall  A  B  C  D,  pG A C D B -> eT C B A C B D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat17sat94sat120sat146sat170sat242sat298 : Sym.

Lemma lemma_PGflipsat0sat6sat18sat95sat121sat147sat171sat243sat299 : forall  A  B  C  D,  pG A B C D -> eT A C B A C D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat18sat95sat121sat147sat171sat243sat299 : Sym.

Lemma axiom_congruentequalsat7sat19sat96sat122sat148sat172sat244sat300 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A C B Cb Cc Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat19sat96sat122sat148sat172sat244sat300 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150sat174sat246sat301 : forall  A  B  C  D,  pG A C D B -> eT C B A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat21sat98sat124sat150sat174sat246sat301 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat22sat99sat125sat151sat175sat247sat302 : forall  A  B  C  D,  pG A B C D -> eT A C B D A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat22sat99sat125sat151sat175sat247sat302 : Sym.

Lemma axiom_congruentequalsat7sat11sat23sat100sat126sat152sat176sat248sat303 : forall  A  B  C  Ca  Cb  Cc,  cong_3 A B C Ca Cb Cc -> eT A C B Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_congruentequalsat7sat11sat23sat100sat126sat152sat176sat248sat303 : Sym.

Lemma proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154sat178sat250sat304 : forall  A  B  C  D,  pG A C D B -> eT C B A B D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_34AuxConjConcl8sat5sat9sat13sat25sat102sat128sat154sat178sat250sat304 : Sym.

Lemma lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155sat179sat251sat305 : forall  A  B  C  D,  pG A B C D -> eT A C B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_PGflipsat0sat6sat10sat14sat26sat103sat129sat155sat179sat251sat305 : Sym.

Lemma axiom_EFpermutationAuxConjConcl12sat306 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl12sat306 : Sym.

Lemma axiom_EFpermutationAuxConjConcl10sat307 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl10sat307 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat308 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat308 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat309 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat309 : Sym.

Lemma axiom_EFpermutationAuxConjConcl4sat310 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl4sat310 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat311 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat311 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat312 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca A D C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat312 : Sym.

Lemma axiom_EFsymmetricsat55sat313 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Ca Cd Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat313 : Sym.

Lemma axiom_EFsymmetricsat56sat314 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Ca Cd Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat314 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat315 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Ca Cd Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat315 : Sym.

Lemma axiom_EFsymmetricsat58sat316 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Ca Cd Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat316 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat317 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Ca Cd Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat317 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat318 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Ca Cd Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat318 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat319 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Ca Cd Cc Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat319 : Sym.

Lemma axiom_EFpermutationAuxConjConcl10sat307sat320 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Cc Cd Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl10sat307sat320 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat308sat321 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Cd Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat308sat321 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat309sat322 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Cb Cc Cd Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat309sat322 : Sym.

Lemma axiom_EFpermutationAuxConjConcl4sat310sat323 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Cc Cb Ca Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl4sat310sat323 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat311sat324 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Cd Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat311sat324 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat312sat325 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF A D C B Cb Ca Cd Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat312sat325 : Sym.

Lemma axiom_EFsymmetricsat56sat314sat326 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat314sat326 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat315sat327 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat315sat327 : Sym.

Lemma axiom_EFsymmetricsat58sat316sat328 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat316sat328 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat317sat329 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat317sat329 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat318sat330 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat318sat330 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat319sat331 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Ca Cd Cc Cb B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat319sat331 : Sym.

Lemma axiom_EFpermutationAuxConjConcl10sat332 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl10sat332 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat333 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat333 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat334 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat334 : Sym.

Lemma axiom_EFpermutationAuxConjConcl4sat335 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl4sat335 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat336 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat336 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat337 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca C B A D.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat337 : Sym.

Lemma axiom_EFsymmetricsat56sat338 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Cc Cb Ca Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat338 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat339 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Cc Cb Ca Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat339 : Sym.

Lemma axiom_EFsymmetricsat58sat340 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Cc Cb Ca Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat340 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat341 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Cc Cb Ca Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat341 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat342 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Cc Cb Ca Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat342 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat343 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Cc Cb Ca Cd.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat343 : Sym.

Lemma axiom_EFpermutationAuxConjConcl10sat307sat320sat344 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl10sat307sat320sat344 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat308sat321sat345 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat308sat321sat345 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat309sat322sat346 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat309sat322sat346 : Sym.

Lemma axiom_EFpermutationAuxConjConcl4sat310sat323sat347 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl4sat310sat323sat347 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat311sat324sat348 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat311sat324sat348 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat312sat325sat349 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat312sat325sat349 : Sym.

Lemma axiom_EFsymmetricsat56sat314sat326sat350 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Cc Cd Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat314sat326sat350 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat315sat327sat351 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Cc Cd Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat315sat327sat351 : Sym.

Lemma axiom_EFsymmetricsat58sat316sat328sat352 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Cc Cd Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat316sat328sat352 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat317sat329sat353 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Cc Cd Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat317sat329sat353 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat318sat330sat354 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Cc Cd Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat318sat330sat354 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat319sat331sat355 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Cc Cd Ca Cb.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat319sat331sat355 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat333sat356 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Cb Ca Cd Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat333sat356 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat334sat357 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Cd Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat334sat357 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat336sat358 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Cb Cc Cd Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat336sat358 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat337sat359 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C B A D Cd Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat337sat359 : Sym.

Lemma axiom_EFsymmetricsat58sat340sat360 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat340sat360 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat341sat361 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat341sat361 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat342sat362 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat342sat362 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat343sat363 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cb Ca Cd D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat343sat363 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat308sat321sat345sat364 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Cb Cc Cd Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat308sat321sat345sat364 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat309sat322sat346sat365 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Cd Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat309sat322sat346sat365 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat311sat324sat348sat366 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Cb Ca Cd Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat311sat324sat348sat366 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat312sat325sat349sat367 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF C D A B Cd Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat312sat325sat349sat367 : Sym.

Lemma axiom_EFsymmetricsat58sat316sat328sat352sat368 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat316sat328sat352sat368 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat317sat329sat353sat369 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat317sat329sat353sat369 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat318sat330sat354sat370 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat318sat330sat354sat370 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat319sat331sat355sat371 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cc Cd Ca Cb D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat319sat331sat355sat371 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat372 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat372 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat373 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat373 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat374 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat374 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat375 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca D A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat375 : Sym.

Lemma axiom_EFsymmetricsat58sat376 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Cd Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat376 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat377 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Cd Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat377 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat378 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Cd Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat378 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat379 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Cd Ca Cb Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat379 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat308sat321sat380 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat308sat321sat380 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat309sat322sat381 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat309sat322sat381 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat311sat324sat382 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat311sat324sat382 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat312sat325sat383 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc B A D C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat312sat325sat383 : Sym.

Lemma axiom_EFsymmetricsat58sat316sat328sat384 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Cb Ca Cd Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat316sat328sat384 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat317sat329sat385 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Cb Ca Cd Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat317sat329sat385 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat318sat330sat386 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Cb Ca Cd Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat318sat330sat386 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat319sat331sat387 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Cb Ca Cd Cc.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat319sat331sat387 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat333sat356sat388 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat333sat356sat388 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat334sat357sat389 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat334sat357sat389 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat336sat358sat390 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat336sat358sat390 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat337sat359sat391 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat337sat359sat391 : Sym.

Lemma axiom_EFsymmetricsat58sat340sat360sat392 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Cd Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat340sat360sat392 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat341sat361sat393 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Cd Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat341sat361sat393 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat342sat362sat394 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Cd Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat342sat362sat394 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat343sat363sat395 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Cd Cc Cb Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat343sat363sat395 : Sym.

Lemma axiom_EFpermutationAuxConjConcl8sat308sat321sat345sat364sat396 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Cc Cd Ca B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl8sat308sat321sat345sat364sat396 : Sym.

Lemma axiom_EFpermutationAuxConjConcl6sat309sat322sat346sat365sat397 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Cc Cb Ca B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl6sat309sat322sat346sat365sat397 : Sym.

Lemma axiom_EFpermutationAuxConjConcl2sat311sat324sat348sat366sat398 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cb Ca Cd Cc B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl2sat311sat324sat348sat366sat398 : Sym.

Lemma axiom_EFpermutationAuxConjConcl0sat312sat325sat349sat367sat399 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF Cd Ca Cb Cc B C D A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFpermutationAuxConjConcl0sat312sat325sat349sat367sat399 : Sym.

Lemma axiom_EFsymmetricsat58sat316sat328sat352sat368sat400 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B C D A Cb Cc Cd Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat58sat316sat328sat352sat368sat400 : Sym.

Lemma axiom_EFsymmetricsat55sat59sat317sat329sat353sat369sat401 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D C B A Cb Cc Cd Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat59sat317sat329sat353sat369sat401 : Sym.

Lemma axiom_EFsymmetricsat56sat60sat318sat330sat354sat370sat402 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF B A D C Cb Cc Cd Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat56sat60sat318sat330sat354sat370sat402 : Sym.

Lemma axiom_EFsymmetricsat55sat57sat61sat319sat331sat355sat371sat403 : forall  A  B  C  D  Ca  Cb  Cc  Cd,  eF A B C D Ca Cb Cc Cd -> eF D A B C Cb Cc Cd Ca.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve axiom_EFsymmetricsat55sat57sat61sat319sat331sat355sat371sat403 : Sym.


Theorem proposition_43 : forall A B C D E F G H K : MyT, pG A B C D -> betS A H D -> betS A E B -> betS D F C -> betS B G C -> betS A K C -> pG E A H K -> pG G K F C -> eF K G B E D F K H.
Proof. 
intros a b c d e f g h i.
intros.
assert (eF d f i a b g i a) by applying (axiom_cutoff1 d f c i a b g c i a) (* from steps: 3, 4, 5, 5, 7, 0 *).
assert (eF f d h i g b e i) by applying (axiom_cutoff2 f d h a i g b e a i) (* from steps: 1, 2, 6, 8 *).
assert (eF f d h i e i g b) by applying (axiom_EFpermutation f d h i g b e i) (* from steps: 9 *).
assert (eF i g b e d f i h) by applying (axiom_EFpermutationAuxConjConcl6sat309sat322sat381 f d h i e i g b) (* from steps: 10 *).
conclude.
Qed.

End Sec.
