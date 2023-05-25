Require Import src.general_tactics.
Require Import Classical.

Section Sec.

Parameter MyT : Type.
Parameter betS : MyT -> MyT -> MyT -> Prop.
Parameter cong : MyT -> MyT -> MyT -> MyT -> Prop.
Parameter equilateral : MyT -> MyT -> MyT -> Prop.
Parameter triangle : MyT -> MyT -> MyT -> Prop.
Parameter col : MyT -> MyT -> MyT -> Prop.
Parameter per : MyT -> MyT -> MyT -> Prop.
Parameter betS_cong_1 : MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter equilateral_triangle_2 : MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_8 : MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_8_betS_8 : MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_8_betS_8_eqnative_8 : MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_8_betS_8_eqnative_8_eqnative_8 : MyT -> MyT -> MyT -> Prop.
Parameter betS_cong_20_cong_20_nnneqnative_20 : MyT -> MyT -> MyT -> MyT -> Prop.

Hypothesis lemma_betweennotequal : forall A B C : MyT, betS A B C -> B <> C /\ A <> B /\ A <> C.
Hypothesis lemma_extension : forall A B P Q : MyT, A <> B -> P <> Q -> exists  X : MyT, betS A B X /\ cong B X P Q.
Hypothesis proposition_01 : forall A B : MyT, A <> B -> exists  X : MyT, equilateral A B X /\ triangle A B X.
Hypothesis defequilateral : forall A B C : MyT, equilateral A B C -> cong A B B C /\ cong B C C A.
Hypothesis defequilateral2 : forall A B C : MyT, cong A B B C -> cong B C C A -> equilateral A B C.
Hypothesis lemma_doublereverse : forall A B C D : MyT, cong A B C D -> cong D C B A /\ cong B A D C.
Hypothesis lemma_congruenceflip : forall A B C D : MyT, cong A B C D -> cong B A D C /\ cong B A C D /\ cong A B D C.
Hypothesis defncollinear : forall A B C : MyT, ~ col A B C -> A <> B /\ A <> C /\ B <> C.
Hypothesis defcollinear : forall A B C : MyT, col A B C -> A = B \/ A = C \/ B = C \/ betS B A C \/ betS A B C \/ betS A C B.
Hypothesis defcollinear2a : forall A B C : MyT, A = B -> col A B C.
Hypothesis defcollinear2b : forall A B C : MyT, A = C -> col A B C.
Hypothesis defcollinear2c : forall A B C : MyT, B = C -> col A B C.
Hypothesis defcollinear2d : forall A B C : MyT, betS B A C -> col A B C.
Hypothesis defcollinear2e : forall A B C : MyT, betS A B C -> col A B C.
Hypothesis defcollinear2f : forall A B C : MyT, betS A C B -> col A B C.
Hypothesis defcollinear2g : forall A B C D : MyT, betS A D B -> triangle A B C -> ~ col A D C /\ ~ col B D C.
Hypothesis lemma_collinearorder : forall A B C : MyT, col A B C -> col B A C /\ col B C A /\ col C A B /\ col A C B /\ col C B A.
Hypothesis deftriangle : forall A B C : MyT, triangle A B C -> ~ col A B C.
Hypothesis deftriangle2 : forall A B C : MyT, ~ col A B C -> triangle A B C.
Hypothesis deftriangle3 : forall A B C : MyT, triangle A B C -> triangle A C B /\ triangle B A C /\ triangle C B A /\ triangle B C A /\ triangle C A B.
Hypothesis defrightangle : forall A B C : MyT, per A B C -> exists  X : MyT, betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C.
Hypothesis defrightangle2 : forall A B C X : MyT, betS A B X -> cong A B X B -> cong A C X C -> B <> C -> per A B C.

Lemma lemma_extensionAuxConjDisj0sat0 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> A <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat0 : Sym.

Lemma defrightangleAuxConjDisj0sat1 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> A <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat1 : Sym.

Lemma lemma_extensionAuxConjDisj0sat2 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> A <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat2 : Sym.

Lemma defrightangleAuxConjDisj0sat3 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> A <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat3 : Sym.

Lemma lemma_extensionAuxConjDisj0sat4 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> B <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat4 : Sym.

Lemma defrightangleAuxConjDisj0sat5 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> B <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat5 : Sym.

Lemma proposition_01AuxConjDisj0sat6 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong B X X A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6 : Sym.

Lemma proposition_01AuxConjDisj0sat7 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong A B B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7 : Sym.

Lemma lemma_extensionAuxConjDisj1sat8 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> cong X B Q P.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj1sat8 : Sym.

Lemma defequilateralAuxConjConcl2sat9 : forall  A  B  C,  equilateral A B C -> cong C B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl2sat9 : Sym.

Lemma defequilateralAuxConjConcl0sat10 : forall  A  B  C,  equilateral A B C -> cong B A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl0sat10 : Sym.

Lemma lemma_doublereverseAuxConjConcl0sat11 : forall  A  B  C  D,  cong A B C D -> cong C D A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_doublereverseAuxConjConcl0sat11 : Sym.

Lemma defrightangleAuxConjDisj2sat12 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong C A C X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj2sat12 : Sym.

Lemma defrightangleAuxConjDisj1sat13 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong B A B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj1sat13 : Sym.

Lemma proposition_01AuxConjDisj0sat6sat14 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong X B A X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6sat14 : Sym.

Lemma proposition_01AuxConjDisj0sat7sat15 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong B A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7sat15 : Sym.

Lemma lemma_extensionAuxConjDisj1sat16 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> cong Q P X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj1sat16 : Sym.

Lemma defequilateralAuxConjConcl2sat17 : forall  A  B  C,  equilateral A B C -> cong A C C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl2sat17 : Sym.

Lemma defequilateralAuxConjConcl0sat18 : forall  A  B  C,  equilateral A B C -> cong C B B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl0sat18 : Sym.

Lemma lemma_congruenceflipAuxConjConcl4sat19 : forall  A  B  C  D,  cong A B C D -> cong C D B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_congruenceflipAuxConjConcl4sat19 : Sym.

Lemma lemma_congruenceflipAuxConjConcl2sat20 : forall  A  B  C  D,  cong A B C D -> cong D C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_congruenceflipAuxConjConcl2sat20 : Sym.

Lemma defrightangleAuxConjDisj2sat21 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong C X C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj2sat21 : Sym.

Lemma defrightangleAuxConjDisj1sat22 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong B X B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj1sat22 : Sym.

Lemma proposition_01AuxConjDisj0sat6sat23 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong A X X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6sat23 : Sym.

Lemma proposition_01AuxConjDisj0sat7sat24 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong X B B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7sat24 : Sym.

Lemma lemma_extensionAuxConjDisj1sat8sat25 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> cong P Q B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj1sat8sat25 : Sym.

Lemma defequilateralAuxConjConcl2sat9sat26 : forall  A  B  C,  equilateral A B C -> cong C A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl2sat9sat26 : Sym.

Lemma defequilateralAuxConjConcl0sat10sat27 : forall  A  B  C,  equilateral A B C -> cong B C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl0sat10sat27 : Sym.

Lemma defrightangleAuxConjDisj2sat12sat28 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong X C A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj2sat12sat28 : Sym.

Lemma defrightangleAuxConjDisj1sat13sat29 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong X B A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj1sat13sat29 : Sym.

Lemma proposition_01AuxConjDisj0sat6sat14sat30 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong X A B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6sat14sat30 : Sym.

Lemma proposition_01AuxConjDisj0sat7sat15sat31 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong B X A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7sat15sat31 : Sym.

Lemma lemma_extensionAuxConjDisj1sat32 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> cong B X Q P.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj1sat32 : Sym.

Lemma defequilateralAuxConjConcl2sat33 : forall  A  B  C,  equilateral A B C -> cong B C A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl2sat33 : Sym.

Lemma defequilateralAuxConjConcl0sat34 : forall  A  B  C,  equilateral A B C -> cong A B C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl0sat34 : Sym.

Lemma defrightangleAuxConjDisj2sat35 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong A C C X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj2sat35 : Sym.

Lemma defrightangleAuxConjDisj1sat36 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong A B B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj1sat36 : Sym.

Lemma proposition_01AuxConjDisj0sat6sat37 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong B X A X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6sat37 : Sym.

Lemma proposition_01AuxConjDisj0sat7sat38 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong A B X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7sat38 : Sym.

Lemma lemma_extensionAuxConjDisj1sat8sat39 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> cong X B P Q.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj1sat8sat39 : Sym.

Lemma defequilateralAuxConjConcl2sat9sat40 : forall  A  B  C,  equilateral A B C -> cong C B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl2sat9sat40 : Sym.

Lemma defequilateralAuxConjConcl0sat10sat41 : forall  A  B  C,  equilateral A B C -> cong B A B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl0sat10sat41 : Sym.

Lemma defrightangleAuxConjDisj2sat12sat42 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong C A X C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj2sat12sat42 : Sym.

Lemma defrightangleAuxConjDisj1sat13sat43 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong B A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj1sat13sat43 : Sym.

Lemma proposition_01AuxConjDisj0sat6sat14sat44 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong X B X A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6sat14sat44 : Sym.

Lemma proposition_01AuxConjDisj0sat7sat15sat45 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong B A B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7sat15sat45 : Sym.

Lemma lemma_extensionAuxConjDisj1sat16sat46 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> cong Q P B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj1sat16sat46 : Sym.

Lemma defequilateralAuxConjConcl2sat17sat47 : forall  A  B  C,  equilateral A B C -> cong A C B C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl2sat17sat47 : Sym.

Lemma defequilateralAuxConjConcl0sat18sat48 : forall  A  B  C,  equilateral A B C -> cong C B A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl0sat18sat48 : Sym.

Lemma defrightangleAuxConjDisj2sat21sat49 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong C X A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj2sat21sat49 : Sym.

Lemma defrightangleAuxConjDisj1sat22sat50 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong B X A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj1sat22sat50 : Sym.

Lemma proposition_01AuxConjDisj0sat6sat23sat51 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong A X B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6sat23sat51 : Sym.

Lemma proposition_01AuxConjDisj0sat7sat24sat52 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong X B A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7sat24sat52 : Sym.

Lemma lemma_extensionAuxConjDisj1sat8sat25sat53 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> cong P Q X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj1sat8sat25sat53 : Sym.

Lemma defequilateralAuxConjConcl2sat9sat26sat54 : forall  A  B  C,  equilateral A B C -> cong C A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl2sat9sat26sat54 : Sym.

Lemma defequilateralAuxConjConcl0sat10sat27sat55 : forall  A  B  C,  equilateral A B C -> cong B C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defequilateralAuxConjConcl0sat10sat27sat55 : Sym.

Lemma defrightangleAuxConjDisj2sat12sat28sat56 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong X C C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj2sat12sat28sat56 : Sym.

Lemma defrightangleAuxConjDisj1sat13sat29sat57 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> cong X B B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj1sat13sat29sat57 : Sym.

Lemma proposition_01AuxConjDisj0sat6sat14sat30sat58 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong X A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat6sat14sat30sat58 : Sym.

Lemma proposition_01AuxConjDisj0sat7sat15sat31sat59 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> cong B X B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj0sat7sat15sat31sat59 : Sym.

Lemma deftrianglesat60 : forall  A  B  C,  triangle A B C -> B <> C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftrianglesat60 : Sym.

Lemma deftrianglesat61 : forall  A  B  C,  triangle A B C -> A <> C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftrianglesat61 : Sym.

Lemma deftrianglesat62 : forall  A  B  C,  triangle A B C -> A <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftrianglesat62 : Sym.

Lemma eq_reflsat63 : forall  A  C,  col A A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_reflsat63 : Sym.

Lemma eq_symsat64 : forall  A  B  C,  A = B -> col B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat64 : Sym.

Lemma eq_reflsat65 : forall  A  B,  col A B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_reflsat65 : Sym.

Lemma eq_symsat66 : forall  A  B,  A = B -> col B B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat66 : Sym.

Lemma eq_reflsat67 : forall  A,  col A A A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_reflsat67 : Sym.

Lemma eq_symsat68 : forall  A  B,  A = B -> col A B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat68 : Sym.

Lemma lemma_extensionAuxConjDisj0sat69 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col B A X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat69 : Sym.

Lemma defrightangleAuxConjDisj0sat70 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> col B A X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat70 : Sym.

Lemma lemma_extensionAuxConjDisj0sat71 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col A B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat71 : Sym.

Lemma defrightangleAuxConjDisj0sat72 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> col A B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat72 : Sym.

Lemma lemma_extensionAuxConjDisj0sat73 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat73 : Sym.

Lemma defrightangleAuxConjDisj0sat74 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> col A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat74 : Sym.

Lemma defcollinear2dsat75 : forall  A  B  C,  betS B A C -> col C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defcollinear2dsat75 : Sym.

Lemma defcollinear2esat76 : forall  A  B  C,  betS A B C -> col C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defcollinear2esat76 : Sym.

Lemma defcollinear2fsat77 : forall  A  B  C,  betS A C B -> col C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defcollinear2fsat77 : Sym.

Lemma eq_symsat66sat78 : forall  A  B,  A = B -> col A B B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat66sat78 : Sym.

Lemma lemma_extensionAuxConjDisj0sat69sat79 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col X A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat69sat79 : Sym.

Lemma defrightangleAuxConjDisj0sat70sat80 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> col X A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat70sat80 : Sym.

Lemma lemma_extensionAuxConjDisj0sat71sat81 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col X B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat71sat81 : Sym.

Lemma defrightangleAuxConjDisj0sat72sat82 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> col X B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat72sat82 : Sym.

Lemma lemma_extensionAuxConjDisj0sat73sat83 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col B X A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat73sat83 : Sym.

Lemma defrightangleAuxConjDisj0sat74sat84 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> col B X A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat74sat84 : Sym.

Lemma eq_symsat66sat85 : forall  A  B,  A = B -> col B A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat66sat85 : Sym.

Lemma eq_symsat68sat86 : forall  A  B,  A = B -> col A A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat68sat86 : Sym.

Lemma eq_symsat68sat86sat87 : forall  A  B,  A = B -> col B A A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat68sat86sat87 : Sym.

Lemma proposition_01AuxConjDisj1sat88 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> ~ col A B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat88 : Sym.

Lemma deftriangle3AuxConjConcl8sat89 : forall  A  B  C,  triangle A B C -> ~ col C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle3AuxConjConcl8sat89 : Sym.

Lemma deftriangle3AuxConjConcl6sat90 : forall  A  B  C,  triangle A B C -> ~ col B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle3AuxConjConcl6sat90 : Sym.

Lemma deftriangle3AuxConjConcl4sat91 : forall  A  B  C,  triangle A B C -> ~ col C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle3AuxConjConcl4sat91 : Sym.

Lemma deftriangle3AuxConjConcl2sat92 : forall  A  B  C,  triangle A B C -> ~ col B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle3AuxConjConcl2sat92 : Sym.

Lemma deftriangle3AuxConjConcl0sat93 : forall  A  B  C,  triangle A B C -> ~ col A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle3AuxConjConcl0sat93 : Sym.

Lemma proposition_01AuxConjDisj1sat94 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> triangle X A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94 : Sym.

Lemma deftriangle2sat95 : forall  A  B  C,  ~ col A B C -> triangle C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat95 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat96 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> triangle B X A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat96 : Sym.

Lemma deftriangle2sat95sat97 : forall  A  B  C,  ~ col A B C -> triangle B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat95sat97 : Sym.

Lemma proposition_01AuxConjDisj1sat98 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> triangle X B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat98 : Sym.

Lemma deftriangle2sat99 : forall  A  B  C,  ~ col A B C -> triangle C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat99 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat100 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> triangle B A X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat100 : Sym.

Lemma deftriangle2sat95sat101 : forall  A  B  C,  ~ col A B C -> triangle B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat95sat101 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat96sat102 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> triangle A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat96sat102 : Sym.

Lemma deftriangle2sat95sat97sat103 : forall  A  B  C,  ~ col A B C -> triangle A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat95sat97sat103 : Sym.

Lemma lemma_betweennotequalAuxConjConcl4sat104 : forall  A  B  C,  betS A B C -> C <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_betweennotequalAuxConjConcl4sat104 : Sym.

Lemma lemma_betweennotequalAuxConjConcl2sat105 : forall  A  B  C,  betS A B C -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_betweennotequalAuxConjConcl2sat105 : Sym.

Lemma lemma_betweennotequalAuxConjConcl0sat106 : forall  A  B  C,  betS A B C -> C <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_betweennotequalAuxConjConcl0sat106 : Sym.

Lemma defncollinearAuxConjConcl4sat107 : forall  A  B  C,  ~ col A B C -> C <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defncollinearAuxConjConcl4sat107 : Sym.

Lemma defncollinearAuxConjConcl2sat108 : forall  A  B  C,  ~ col A B C -> C <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defncollinearAuxConjConcl2sat108 : Sym.

Lemma defncollinearAuxConjConcl0sat109 : forall  A  B  C,  ~ col A B C -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defncollinearAuxConjConcl0sat109 : Sym.

Lemma defrightangleAuxConjDisj3sat110 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> C <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj3sat110 : Sym.

Lemma lemma_extensionAuxConjDisj0sat0sat111 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> X <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat0sat111 : Sym.

Lemma defrightangleAuxConjDisj0sat1sat112 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> X <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat1sat112 : Sym.

Lemma lemma_extensionAuxConjDisj0sat2sat113 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat2sat113 : Sym.

Lemma defrightangleAuxConjDisj0sat3sat114 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat3sat114 : Sym.

Lemma lemma_extensionAuxConjDisj0sat4sat115 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> X <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat4sat115 : Sym.

Lemma defrightangleAuxConjDisj0sat5sat116 : forall  A  B  X  C,  betS A B X /\ cong A B X B /\ cong A C X C /\ B <> C -> X <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defrightangleAuxConjDisj0sat5sat116 : Sym.

Lemma deftrianglesat60sat117 : forall  A  B  C,  triangle A B C -> C <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftrianglesat60sat117 : Sym.

Lemma deftrianglesat61sat118 : forall  A  B  C,  triangle A B C -> C <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftrianglesat61sat118 : Sym.

Lemma deftrianglesat62sat119 : forall  A  B  C,  triangle A B C -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftrianglesat62sat119 : Sym.

Lemma proposition_01AuxConjDisj1sat120 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> B <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat120 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat121 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> A <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat121 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat96sat122 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> X <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat96sat122 : Sym.

Lemma proposition_01AuxConjDisj1sat98sat123 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat98sat123 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat100sat124 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> A <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat100sat124 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat96sat102sat125 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> X <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat96sat102sat125 : Sym.

Lemma proposition_01AuxConjDisj1sat126 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> ~ col X A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat126 : Sym.

Lemma deftriangle2sat127 : forall  A  B  C,  ~ col A B C -> ~ col C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat127 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat128 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> ~ col B X A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat128 : Sym.

Lemma deftriangle2sat95sat129 : forall  A  B  C,  ~ col A B C -> ~ col B C A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat95sat129 : Sym.

Lemma proposition_01AuxConjDisj1sat98sat130 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> ~ col A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat98sat130 : Sym.

Lemma deftriangle2sat99sat131 : forall  A  B  C,  ~ col A B C -> ~ col A C B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat99sat131 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat100sat132 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> ~ col X B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat100sat132 : Sym.

Lemma deftriangle2sat95sat101sat133 : forall  A  B  C,  ~ col A B C -> ~ col C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat95sat101sat133 : Sym.

Lemma proposition_01AuxConjDisj1sat94sat96sat102sat134 : forall  A  B  X,  equilateral A B X /\ triangle A B X -> ~ col B A X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve proposition_01AuxConjDisj1sat94sat96sat102sat134 : Sym.

Lemma deftriangle2sat95sat97sat103sat135 : forall  A  B  C,  ~ col A B C -> ~ col B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftriangle2sat95sat97sat103sat135 : Sym.


Theorem proposition_11 : forall A B C : MyT, betS A C B -> exists  X : MyT, per A C X.
Proof. 
intros a b c.
intros.
let Tf:=fresh in
assert (Tf:exists w, betS a c w /\ cong c w a c) by applying (lemma_extension a c a c) (* from steps: 0, 0 *); destruct Tf as [w];spliter. spliter.
let Tf:=fresh in
assert (Tf:exists w1, equilateral a w w1 /\ triangle a w w1) by applying (proposition_01 a w) (* from steps: 1 *); destruct Tf as [w1];spliter. spliter.
assert (~ col a c w1) by applying (defcollinear2g a w w1 c) (* from steps: 1, 2 *).
assert (per a c w1) by applying (defrightangle2 a c w1 w) (* from steps: 1, 1, 2, 3 *).
conclude.
Qed.

End Sec.
