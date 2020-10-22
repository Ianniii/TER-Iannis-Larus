From Test Require Import tactic.

Section FOFProblem.

Variable Universe : Set.
Variable UniverseElement : Universe.

Variable p_ : Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Universe -> Prop.
Variable goal_ : Prop.
Variable dom_ : Universe -> Prop.

Variable a9_ : Universe.
Variable a8_ : Universe.
Variable a7_ : Universe.
Variable a6_ : Universe.
Variable a5_ : Universe.
Variable a4_ : Universe.
Variable a3_ : Universe.
Variable a20_ : Universe.
Variable a2_ : Universe.
Variable a19_ : Universe.
Variable a18_ : Universe.
Variable a17_ : Universe.
Variable a16_ : Universe.
Variable a15_ : Universe.
Variable a14_ : Universe.
Variable a13_ : Universe.
Variable a12_ : Universe.
Variable a11_ : Universe.
Variable a10_ : Universe.
Variable a1_ : Universe.

Variable ax1_1 : (dom_ a1_ /\ (dom_ a2_ /\ (dom_ a3_ /\ (dom_ a4_ /\ (dom_ a5_ /\ (dom_ a6_ /\ (dom_ a7_ /\ (dom_ a8_ /\ (dom_ a9_ /\ (dom_ a10_ /\ (dom_ a11_ /\ (dom_ a12_ /\ (dom_ a13_ /\ (dom_ a14_ /\ (dom_ a15_ /\ (dom_ a16_ /\ (dom_ a17_ /\ (dom_ a18_ /\ (dom_ a19_ /\ dom_ a20_))))))))))))))))))).
Variable ax2_2 : (forall A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 : Universe, ((dom_ A1 /\ (dom_ A2 /\ (dom_ A3 /\ (dom_ A4 /\ (dom_ A5 /\ (dom_ A6 /\ (dom_ A7 /\ (dom_ A8 /\ (dom_ A9 /\ (dom_ A10 /\ (dom_ A11 /\ (dom_ A12 /\ (dom_ A13 /\ (dom_ A14 /\ (dom_ A15 /\ (dom_ A16 /\ (dom_ A17 /\ (dom_ A18 /\ (dom_ A19 /\ dom_ A20))))))))))))))))))) -> p_ A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20)).
Variable ax3_3 : (p_ a20_ a19_ a18_ a17_ a16_ a15_ a14_ a13_ a12_ a11_ a10_ a9_ a8_ a7_ a6_ a5_ a4_ a3_ a2_ a1_ -> goal_).

Theorem lemma20_4 : goal_.
Proof.
  time tac.
Qed.

End FOFProblem.
