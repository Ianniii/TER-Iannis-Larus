Require Import src.general_tactics.
Require Import Classical.

Section Sec.

Parameter MyT : Type.
Parameter betS : MyT -> MyT -> MyT -> Prop.

Hypothesis axiom_betweennesssymmetry : forall A B C : MyT, betS A B C -> betS C B A.
Hypothesis axiom_innertransitivity : forall A B C D : MyT, betS A B D -> betS B C D -> betS A B C.


Theorem lemma_3_6a : forall A B C D : MyT, betS A B C -> betS A C D -> betS B C D.
Proof. 
intros a b c d.
intros.
assert (betS d c b) by applying (axiom_innertransitivity d c b a) (* from steps: 1, 0 *).
assert (betS b c d) by applying (axiom_betweennesssymmetry d c b) (* from steps: 2 *).
conclude.
Qed.

End Sec.
