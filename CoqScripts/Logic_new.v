Section Logic.
Variables A B C : Prop.

Lemma ax0: A -> A.
Proof.
  intro. assumption.
Qed.
Check ax0.
Print ax0.

Lemma ax1 : A -> B -> A.
Proof.
  (* intro. intro. *)
  intros HA HB.
  assumption.
Qed.
Print ax1.

Lemma ax2 : (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  intros HAB HABC HA.
  apply HABC.
  - assumption.
  - apply HAB. assumption.
Qed.
Print ax2.

Check and.
Print and.

Lemma ax3 : A /\ B -> A.
Proof.
  intro. destruct H as [HA HB].
  assumption.
Qed.
Print ax3.

Lemma ax4 : A /\ B -> B.
Proof.
  intro. destruct H as [HA HB].
  assumption.
Qed.

Lemma ax5 : (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
  intros HAB HAC HA.
  (* constructor. *) split.
  - apply HAB. assumption.
  - apply HAC. assumption.
Qed.
Print ax5.

Check or.
Print or.

Lemma ax6 : A -> A \/ B.
Proof.
  intro. constructor. assumption.
Qed.
Print ax6.

Lemma ax7 : B -> A \/ B.
Proof.
  intro. constructor 2. assumption.
Qed.
Print ax7.

Lemma ax8 : (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros HAC HBC HAorB. destruct HAorB as [HA | HB].
  - apply HAC. assumption.
  - apply HBC. assumption.
Qed.
Print ax8.

Lemma ax9 : (A -> ~ B) -> B -> ~ A.
Proof.
  intros HAnB HB. unfold "~ _" in HAnB |-*. intro HA.
  apply HAnB (*.
  - assumption.
  - assumption. *); assumption.
Qed.
Print ax9.
End Logic.

Check ax8.
