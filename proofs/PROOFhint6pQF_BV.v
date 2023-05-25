Require Import src.general_tactics.
Require Import Classical.

Section Sec.

Parameter MyT : Type.
Parameter per : MyT -> MyT -> MyT -> Prop.
Parameter col : MyT -> MyT -> MyT -> Prop.
Parameter betS : MyT -> MyT -> MyT -> Prop.
Parameter cong : MyT -> MyT -> MyT -> MyT -> Prop.
Parameter out : MyT -> MyT -> MyT -> Prop.
Parameter supp : MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter congA : MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter rT : MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter oS : MyT -> MyT -> MyT -> MyT -> Prop.
Parameter par : MyT -> MyT -> MyT -> MyT -> Prop.
Parameter betS_cong_2 : MyT -> MyT -> MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_3 : MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_3_betS_3 : MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_3_betS_3_eqnative_3 : MyT -> MyT -> MyT -> Prop.
Parameter betS_betS_3_betS_3_eqnative_3_eqnative_3 : MyT -> MyT -> MyT -> Prop.
Parameter supp_congA_20_congA_20 : MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> MyT -> Prop.

Hypothesis lemma_rightangleNC : forall A B C : MyT, per A B C -> ~ col A B C.
Hypothesis lemma_NCdistinct : forall A B C : MyT, ~ col A B C -> A <> B /\ B <> C /\ A <> C /\ B <> A /\ C <> B /\ C <> A.
Hypothesis lemma_extension : forall A B P Q : MyT, A <> B -> P <> Q -> exists  X : MyT, betS A B X /\ cong B X P Q.
Hypothesis defcollinear : forall A B C : MyT, col A B C -> A = B \/ A = C \/ B = C \/ betS B A C \/ betS A B C \/ betS A C B.
Hypothesis defcollinear2a : forall A B C : MyT, A = B -> col A B C.
Hypothesis defcollinear2b : forall A B C : MyT, A = C -> col A B C.
Hypothesis defcollinear2c : forall A B C : MyT, B = C -> col A B C.
Hypothesis defcollinear2d : forall A B C : MyT, betS B A C -> col A B C.
Hypothesis defcollinear2e : forall A B C : MyT, betS A B C -> col A B C.
Hypothesis defcollinear2f : forall A B C : MyT, betS A C B -> col A B C.
Hypothesis lemma_betweennotequal : forall A B C : MyT, betS A B C -> B <> C /\ A <> B /\ A <> C.
Hypothesis lemma_inequalitysymmetric : forall A B : MyT, A <> B -> B <> A.
Hypothesis lemma_collinearright : forall A B C D : MyT, per A B D -> col A B C -> C <> B -> per C B D.
Hypothesis lemma_8_2 : forall A B C : MyT, per A B C -> per C B A.
Hypothesis lemma_ray4_1 : forall A B E : MyT, betS A E B -> A <> B -> out A B E.
Hypothesis lemma_ray4_2 : forall A B E : MyT, E = B -> A <> B -> out A B E.
Hypothesis lemma_ray4_3 : forall A B E : MyT, betS A B E -> A <> B -> out A B E.
Hypothesis defsupplement : forall A B C D F : MyT, supp A B C D F -> out B C D /\ betS A B F.
Hypothesis defsupplement2 : forall A B C D F : MyT, out B C D -> betS A B F -> supp A B C D F.
Hypothesis lemma_Euclid4 : forall A B C Xa Xb Xc : MyT, per A B C -> per Xa Xb Xc -> congA A B C Xa Xb Xc.
Hypothesis deftworightangles : forall A B C D E F : MyT, rT A B C D E F -> exists  X Y Z U V : MyT, supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z.
Hypothesis deftworightangles2 : forall A B C D E F X Y Z U V : MyT, supp X Y U V Z -> congA A B C X Y U -> congA D E F V Y Z -> rT A B C D E F.
Hypothesis proposition_28C : forall B D G H : MyT, rT B G H G H D -> oS B D G H -> par G B H D.
Hypothesis lemma_parallelsymmetric : forall A B C D : MyT, par A B C D -> par C D A B.
Hypothesis lemma_parallelflip : forall A B C D : MyT, par A B C D -> par B A C D /\ par A B D C /\ par B A D C.

Lemma lemma_8_2sat0 : forall  A  B  C,  per A B C -> ~ col C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_8_2sat0 : Sym.

Lemma lemma_rightangleNCsat1 : forall  A  B  C,  per A B C -> C <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_rightangleNCsat1 : Sym.

Lemma lemma_8_2sat0sat2 : forall  A  B  C,  per A B C -> A <> C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_8_2sat0sat2 : Sym.

Lemma lemma_rightangleNCsat3 : forall  A  B  C,  per A B C -> C <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_rightangleNCsat3 : Sym.

Lemma lemma_8_2sat0sat4 : forall  A  B  C,  per A B C -> A <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_8_2sat0sat4 : Sym.

Lemma lemma_rightangleNCsat5 : forall  A  B  C,  per A B C -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_rightangleNCsat5 : Sym.

Lemma lemma_8_2sat0sat6 : forall  A  B  C,  per A B C -> B <> C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_8_2sat0sat6 : Sym.

Lemma eq_reflsat7 : forall  A  C,  col A A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_reflsat7 : Sym.

Lemma eq_symsat8 : forall  A  B  C,  A = B -> col B A C.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat8 : Sym.

Lemma eq_reflsat9 : forall  A  B,  col A B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_reflsat9 : Sym.

Lemma eq_symsat10 : forall  A  B,  A = B -> col B B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat10 : Sym.

Lemma eq_reflsat11 : forall  A,  col A A A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_reflsat11 : Sym.

Lemma eq_symsat12 : forall  A  B,  A = B -> col A B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat12 : Sym.

Lemma lemma_extensionAuxConjDisj0sat13 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col B A X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat13 : Sym.

Lemma defsupplementAuxConjConcl2sat14 : forall  A  B  C  D  F,  supp A B C D F -> col B A F.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat14 : Sym.

Lemma lemma_extensionAuxConjDisj0sat15 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col A B X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat15 : Sym.

Lemma defsupplementAuxConjConcl2sat16 : forall  A  B  C  D  F,  supp A B C D F -> col A B F.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat16 : Sym.

Lemma lemma_extensionAuxConjDisj0sat17 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> col A X B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat17 : Sym.

Lemma defsupplementAuxConjConcl2sat18 : forall  A  B  C  D  F,  supp A B C D F -> col A F B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat18 : Sym.

Lemma lemma_extensionAuxConjDisj0sat19 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> A <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat19 : Sym.

Lemma defsupplementAuxConjConcl2sat20 : forall  A  B  C  D  F,  supp A B C D F -> A <> F.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat20 : Sym.

Lemma lemma_extensionAuxConjDisj0sat21 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> A <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat21 : Sym.

Lemma defsupplementAuxConjConcl2sat22 : forall  A  B  C  D  F,  supp A B C D F -> A <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat22 : Sym.

Lemma lemma_extensionAuxConjDisj0sat23 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> B <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat23 : Sym.

Lemma defsupplementAuxConjConcl2sat24 : forall  A  B  C  D  F,  supp A B C D F -> B <> F.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat24 : Sym.

Lemma lemma_betweennotequalAuxConjConcl4sat25 : forall  A  B  C,  betS A B C -> C <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_betweennotequalAuxConjConcl4sat25 : Sym.

Lemma lemma_betweennotequalAuxConjConcl2sat26 : forall  A  B  C,  betS A B C -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_betweennotequalAuxConjConcl2sat26 : Sym.

Lemma lemma_betweennotequalAuxConjConcl0sat27 : forall  A  B  C,  betS A B C -> C <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_betweennotequalAuxConjConcl0sat27 : Sym.

Lemma lemma_extensionAuxConjDisj0sat19sat28 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> X <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat19sat28 : Sym.

Lemma defsupplementAuxConjConcl2sat20sat29 : forall  A  B  C  D  F,  supp A B C D F -> F <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat20sat29 : Sym.

Lemma lemma_extensionAuxConjDisj0sat21sat30 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat21sat30 : Sym.

Lemma defsupplementAuxConjConcl2sat22sat31 : forall  A  B  C  D  F,  supp A B C D F -> B <> A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat22sat31 : Sym.

Lemma lemma_extensionAuxConjDisj0sat23sat32 : forall  A  B  X  P  Q,  betS A B X /\ cong B X P Q -> X <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_extensionAuxConjDisj0sat23sat32 : Sym.

Lemma defsupplementAuxConjConcl2sat24sat33 : forall  A  B  C  D  F,  supp A B C D F -> F <> B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve defsupplementAuxConjConcl2sat24sat33 : Sym.

Lemma deftworightanglesAuxConjDisj0sat34 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> betS X Y Z.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat34 : Sym.

Lemma deftworightanglesAuxConjDisj0sat35 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> out Y U V.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat35 : Sym.

Lemma lemma_parallelflipAuxConjConcl4sat36 : forall  A  B  C  D,  par A B C D -> par D C B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_parallelflipAuxConjConcl4sat36 : Sym.

Lemma lemma_parallelflipAuxConjConcl2sat37 : forall  A  B  C  D,  par A B C D -> par D C A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_parallelflipAuxConjConcl2sat37 : Sym.

Lemma lemma_parallelflipAuxConjConcl0sat38 : forall  A  B  C  D,  par A B C D -> par C D B A.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve lemma_parallelflipAuxConjConcl0sat38 : Sym.

Lemma eq_symsat39 : forall  A  B,  A = B -> col A A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat39 : Sym.

Lemma eq_symsat40 : forall  A  B,  A = B -> col B A B.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve eq_symsat40 : Sym.

Lemma deftworightanglesAuxConjDisj0sat41 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> col Y X Z.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat41 : Sym.

Lemma deftworightanglesAuxConjDisj0sat42 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> col X Y Z.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat42 : Sym.

Lemma deftworightanglesAuxConjDisj0sat43 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> col X Z Y.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat43 : Sym.

Lemma deftworightanglesAuxConjDisj0sat44 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> X <> Z.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat44 : Sym.

Lemma deftworightanglesAuxConjDisj0sat45 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> X <> Y.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat45 : Sym.

Lemma deftworightanglesAuxConjDisj0sat46 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> Y <> Z.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat46 : Sym.

Lemma deftworightanglesAuxConjDisj0sat34sat47 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> Z <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat34sat47 : Sym.

Lemma deftworightanglesAuxConjDisj0sat34sat48 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> Y <> X.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat34sat48 : Sym.

Lemma deftworightanglesAuxConjDisj0sat34sat49 : forall  X  Y  U  V  Z  A  B  C  D  E  F,  supp X Y U V Z /\ congA A B C X Y U /\ congA D E F V Y Z -> Z <> Y.
Proof.
inline_lemma_solver.
Qed.

Hint Resolve deftworightanglesAuxConjDisj0sat34sat49 : Sym.


Theorem lemma_twoperpsparallel : forall A B C D : MyT, per A B C -> per B C D -> oS A D B C -> par A B C D.
Proof. 
intros a b c d.
intros.
assert (~ col b c d) by applying (lemma_rightangleNC b c d) (* from steps: 1 *).
assert (out c d d) by applying (lemma_ray4_2 c d d) (* from steps: 1 *).
let Tf:=fresh in
assert (Tf:exists w, betS b c w /\ cong c w b c) by applying (lemma_extension b c b c) (* from steps: 3, 0 *); destruct Tf as [w];spliter. spliter.
assert (per w c d) by applying (lemma_collinearright b c w d) (* from steps: 1, 5, 5 *).
assert (supp b c d d w) by applying (defsupplement2 b c d d w) (* from steps: 4, 5 *).
assert (congA a b c b c d) by applying (lemma_Euclid4 a b c b c d) (* from steps: 0, 1 *).
assert (congA b c d d c w) by applying (lemma_Euclid4 b c d d c w) (* from steps: 1, 6 *).
assert (rT a b c b c d) by applying (deftworightangles2 a b c b c d b c w d d) (* from steps: 7, 8, 9 *).
assert (par b a c d) by applying (proposition_28C a d b c) (* from steps: 10, 2 *).
assert (par c d a b) by applying (lemma_parallelflipAuxConjConcl0sat38 b a c d) (* from steps: 11 *).
assert (par a b c d) by applying (lemma_parallelsymmetric c d a b) (* from steps: 12 *).
conclude.
Qed.

End Sec.
