Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  intro b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Check negb_involutive.
Print negb_involutive.

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

Lemma ax1': A -> B -> B.
Admitted.

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

Lemma ax3' : A /\ B -> B.
Admitted.

Lemma ax4 : (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
  intros HAB HAC HA.
  (* constructor. *) split.
  - apply HAB. assumption.
  - apply HAC. assumption.
Qed.
Print ax4.

Check or.
Print or.

Lemma ax5 : A -> A \/ B.
Proof.
  intro. constructor. assumption.
Qed.
Print ax5.

Lemma ax5' : B -> A \/ B.
Admitted.

Lemma ax6 : (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros HAC HBC HAorB. destruct HAorB as [HA | HB].
  - apply HAC. assumption.
  - apply HBC. assumption.
Qed.
Print ax6.

Lemma ax7 : (A -> ~ B) -> B -> ~ A.
Proof.
  intros HAnB HB. unfold "~ _" in HAnB |-*. intro HA.
  apply HAnB (*.
  - assumption.
  - assumption. *); assumption.
Qed.
Print ax7.
End Logic.

Check ax7.
Print ax7.

(*
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "n + m" := (plus n m) (at level 50, left associativity).
*)
Lemma O_plus_n: forall n: nat, O + n = n.
Proof.
  intro. reflexivity.
Qed.

Lemma n_plus_O: forall n: nat, n + O = n.
Proof.
  intro.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma plus_assoc: forall n m k: nat, (n + m) + k = n + (m + k).
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - intros. simpl. rewrite <- (IHn' m k). reflexivity.
Qed.

Lemma plus_comm: forall n m: nat, n + m = m + n.
Proof.
  induction n as [| n' IHn']; intros.
  - simpl. symmetry. apply n_plus_O.
  - simpl.
    induction m as [| m' IHm'].
    + simpl. rewrite (n_plus_O n'). reflexivity.
    + simpl. f_equal. rewrite (IHn' (S m')). simpl.
      rewrite <- IHm'. rewrite (IHn' m'). reflexivity.
Qed.

(*
Fixpoint mult (n m: nat): nat :=
  match n with
  | O => O
  | S n' => (mult n' m) + m
  end.

Notation "n * m" := (mult n m) (at level 50, left associativity).
*)

Lemma O_mult_n: forall n: nat, 0 * n = 0.
Admitted.

Lemma n_mult_O: forall n: nat, n * 0 = 0.
Admitted.

Lemma one_mult_n: forall n: nat, 1 * n = n.
Admitted.

Lemma n_mult_one: forall n: nat, n * 1 = 1.
Admitted.

Lemma mult_assoc: forall n m k: nat, (n * m) * k = n * (m * k).
Admitted.

Lemma mult_comm: forall n m: nat, n * m = m * n.
Admitted.

Lemma mult_distr_plus: forall n m k: nat, (n + m) * k = n * k + m * k.
Proof.
  induction n, m.
  - intros. simpl. reflexivity.
  - intro. simpl. reflexivity.
  - intro. simpl. rewrite (n_plus_O n).
    rewrite n_plus_O. reflexivity.
  - intro. simpl.
    rewrite (IHn (S m) k). simpl.
    rewrite <- plus_assoc. reflexivity.
Qed.


