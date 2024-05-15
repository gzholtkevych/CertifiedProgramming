(* Тріада: терм - тип - сорт, де сорт є або Set, або Prop, або Type.
   Все є терми, деякі з термів є типами.
   Сорти - це спеціальні типові константи Set, Prop та Type.
   Сорт Type насправді індексований натуральними числами
      Type_0, ..., Type_k, ..., але індекс завжди прихований.
   Кожний терм t населяє певний тип T, що позначається через t : T.
   Наприклад, Set : Type_0, Prop : Type_0, Type_k : Type_{k+1}.
   Наспроавді постулюється справедливість таких суджень:
      Set : Type_0
      Prop : Type_0
      Type_n : Type_m, якщо n < m
   та для будь-якого типу T
      T : Type_0, якщо T : Set
      T : Type_0, якщо T : Prop
      T : Type_m якщо T : T_n та n < m
*)

Check Set.
Check Prop.
Check Type.

Section SecName.
Variable T : Type.
Hypothesis tnd : forall P : Prop, P \/ ~ P.
Check T.
Check tnd.
End SecName.
Fail Check T.
Fail Check tnd.

Locate False.
Locate True.
Check False.
Print Term False.
Check False_ind.

Check True.
Print Term True.
Check True_ind.

Check bool.
Print Term bool.
Check bool_ind.

Section bool_and_Prop.
Variable X : Type.

Definition P (ch : X -> bool) : X -> Prop :=
  fun x => ch x = true.
Check P _.

Lemma P_ch_dec : forall ch x, (P ch x \/ ~ P ch x).
Proof.
  intros. unfold P.
  case (ch x).
  - (* case ch x = true *)
    left. reflexivity.
  - (* case ch x = false *)
    right. intro. discriminate H.
Qed.
End bool_and_Prop.
Check P.
Check P_ch_dec.

Check and.
Print Term and.
Check and_ind.

Section andProperties.
Variables A B C : Prop.

Lemma and_comm : A /\ B <-> B /\ A.
Proof.
  split; intro.
  - elim H. intros HA HB.
    (* pose (HBA := conj HB HA). exact HBA.   *)
    split.
    + assumption.
    + assumption.
  - elim H. intros HB HA.
    split; assumption.
Qed.

Lemma and_comm' : A /\ B <-> B /\ A.
Proof. split; intro; elim H; intros; split; assumption. Qed.

Print Term and_comm.
Print Term and_comm'.

Lemma and_assoc : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split; intro H.
  - elim H. intros. elim H0. intros. split.
    + assumption.
    + split.
      * assumption.
      * assumption.
  - elim H. intros. elim H1. intros; split; [ split; assumption | assumption ].
Qed.

Lemma and_assoc' : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split; intro H; elim H; intros; [elim H0 | elim H1];
  intros; repeat split; assumption.
Qed.

Print Term and_assoc.
Print Term and_assoc'.

End andProperties.

Check and_comm.
Check and_assoc.

Check or.
Print Term or.
Check or_ind.

Section orProperties.
Variables A B C : Prop.

Lemma or_comm : A \/ B <-> B \/ A.
Proof.
  split; intro; elim H; intro;
(*  - right. assumption.
  - left. assumption.
  - right. assumption.
  - left. assumption. *)
  (right; assumption) || (left; assumption).
Qed.

Lemma or_assoc: (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split; intro; elim H; intro; try (elim H0; intro);
  (repeat left; assumption) ||
    (repeat right; assumption) ||
    (right; left; assumption) ||
    (left; right; assumption). 
Qed.

End orProperties.

Print Term or_comm.
Print Term or_assoc.


Section PLaxioms.
Variables A B C : Prop.

Lemma ax1 (*16*) : A -> B -> A.
Admitted.

Lemma ax2 : (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  intros H1 H2 H3. apply H2.
  - assumption.
(*  - apply H1. assumption. *)
  - pose (H := H1 H3). assumption.
Qed.

Lemma ax3 (*16*) : A /\ B -> A.
Admitted.

Lemma ax4 (*16*) : A /\ B -> B.
Admitted.

Lemma ax5 : (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
  intros H1 H2 H3. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

   Lemma ax6 (*16*) : A -> A \/ B.
Admitted.

Lemma ax7 (*16*) : B -> A \/ B.
Admitted.

   Lemma ax8 : (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros H1 H2 H3.
  elim H3; intro H.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax9 (*20*) : (A -> ~ B) -> B -> ~ A.
Admitted.

End PLaxioms.
