(* Завдання № 1:
   -------------------------------------------------------------------------
   У цьому файлі доведіть недоведені твердження:
     ax1, ax3, ax4, ax6, ax7 та ax9.
*)

Section PLaxioms.
Variables A B C : Prop.

Lemma ax1 : A -> B -> A.  (* замінити Admitted на Proof. <доведення> Qed. *)
Admitted.

Lemma ax2 : (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  intros H1 H2 H3. apply H2.
  - assumption.
(*  - apply H1. assumption. *)
  - pose (H := H1 H3). assumption.
Qed.

Lemma ax3 : A /\ B -> A.  (* замінити Admitted на Proof. <доведення> Qed. *)
Admitted.

Lemma ax4 : A /\ B -> B.  (* замінити Admitted на Proof. <доведення> Qed. *)
Admitted.

Lemma ax5 : (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
  intros H1 H2 H3. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax6 : A -> A \/ B.  (* замінити Admitted на Proof. <доведення> Qed. *)
Admitted.

Lemma ax7 : B -> A \/ B.  (* замінити Admitted на Proof. <доведення> Qed. *)
Admitted.

Lemma ax8 : (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros H1 H2 H3.
  elim H3; intro H.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax9 : (A -> ~ B) -> B -> ~ A.  (* замінити Admitted на 
  Proof. <доведення> Qed. *)
Admitted.

End PLaxioms.
