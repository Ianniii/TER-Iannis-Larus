From Test Require Import tactic.

Section FOFProblem.

Variable Universe : Set.
Variable UniverseElement : Universe.

Variable col_ : Universe -> Universe -> Universe -> Prop.
Variable betS_ : Universe -> Universe -> Universe -> Prop.


Variable defcollinear_1 : (forall A B C : Universe, (col_ A B C -> (A = B \/ (A = C \/ (B = C \/ (betS_ B A C \/ (betS_ A B C \/ betS_ A C B))))))).
Variable defcollinear2a_2 : (forall A B C : Universe, (A = B -> col_ A B C)).
Variable defcollinear2b_3 : (forall A B C : Universe, (A = C -> col_ A B C)).
Variable defcollinear2c_4 : (forall A B C : Universe, (B = C -> col_ A B C)).
Variable defcollinear2d_5 : (forall A B C : Universe, (betS_ B A C -> col_ A B C)).
Variable defcollinear2e_6 : (forall A B C : Universe, (betS_ A B C -> col_ A B C)).
Variable defcollinear2f_7 : (forall A B C : Universe, (betS_ A C B -> col_ A B C)).
Variable lemma_collinear4_8 : (forall A B C D : Universe, ((col_ A B C /\ (col_ A B D /\ A <> B)) -> col_ B C D)).
Variable lemma_inequalitysymmetric_9 : (forall A B : Universe, (A <> B -> B <> A)).
Variable lemma_collinearorder_10 : (forall A B C : Universe, (col_ A B C -> (col_ B A C /\ (col_ B C A /\ (col_ C A B /\ (col_ A C B /\ col_ C B A)))))).
Variable lemma_collinear5_11 : (forall A B C D E : Universe, ((A <> B /\ (col_ A B C /\ (col_ A B D /\ col_ A B E))) -> col_ C D E)).

Theorem lemma_NChelper_12 : (forall A B C P Q : Universe, ((~(col_ A B C) /\ (col_ A B P /\ (col_ A B Q /\ P <> Q))) -> ~(col_ P Q C))).
Proof.
  time tac.
Qed.

End FOFProblem.
