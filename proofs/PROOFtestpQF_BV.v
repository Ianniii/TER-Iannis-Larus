Require Import src.general_tactics.
Require Import Classical.

Section Sec.

Parameter MyT : Type.
Parameter betS : MyT -> MyT -> MyT -> Prop.

Hypothesis axiom_betweennesssymmetry : forall A B C : MyT, betS A B C -> betS C B A.
Hypothesis lemma_3_5b : forall A B C D : MyT, betS A B D -> betS B C D -> betS A C D.


Theorem lemma_3_6b : forall A B C D : MyT, betS A B C -> betS A C D -> betS A B D.
Proof. 
intros a b c d.
intros.
assert (betS d b a) by applying (lemma_3_5b d c b a) (* from steps: 1, 0 *).
assert (betS a b d) by applying (axiom_betweennesssymmetry d b a) (* from steps: 2 *).
conclude.
Qed.

End Sec.
