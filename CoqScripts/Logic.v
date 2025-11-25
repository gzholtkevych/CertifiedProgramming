(* Тріада: терм - тип - сорт, де сорт є або Set, або Prop, або Type.
   Все є терми, деякі з термів є типами.
   Сорти - це спеціальні типові константи Set, Prop та Type.
   Сорт Type насправді індексований натуральними числами
      Type_1, ..., Type_k, ..., але індекс завжди прихований.
   Кожний терм t населяє певний тип T, що позначається через t : T.
*)

(*
Section SecName.
Variable T : Type.
Hypothesis tnd : forall P : Prop, P \/ ~ P.
Check T.
Print T.
Check tnd.
Print tnd.
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

Locate bool.
Check bool.
Print Term bool.
Check bool_ind.

Check true.
Print Term true.

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
    right. unfold "_ <> _". intro. discriminate H.
Qed.
End bool_and_Prop.
Check P.
Check P_ch_dec.
Print P_ch_dec.
*)
Locate False.
Check False.
Print False.

Locate True.
Check True.
Print True.
Check I.
Print I.

Locate and.
Check and.
Print and.

Section andProperties.
Variables A B C : Prop.

Lemma and_comm : A /\ B <-> B /\ A.
Proof.
  split.
  1: {
    intro. destruct H as (HA, HB).
    (* pose (HBA := conj HB HA). exact HBA. *)
    split.
    1: { assumption. }
    assumption. }
  intro. destruct H as (HA, HB).
  split.
  1: { assumption. }
  assumption.
Qed.

Lemma and_comm' : A /\ B <-> B /\ A.
Proof. split; intro; destruct H; split; assumption. Qed.

Print Term and_comm.
Print Term and_comm'.

Lemma and_assoc : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split; intro.
  - destruct H as (HAB, HC). destruct HAB as (HA, HB).
    repeat split; assumption.
  - destruct H as (HA, HBC). destruct HBC as (HB, HC).
    repeat split; assumption.
Qed.

Lemma and_assoc' : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split; intro; destruct H as (H1, H2); [destruct H1 | destruct H2];
  repeat split; assumption.
Qed.

Print Term and_assoc.
Print Term and_assoc'.

End andProperties.

Check and_comm.
Check and_assoc.

Locate or.
Check or.
Print or.

Section orProperties.
Variables A B C : Prop.

Lemma or_comm : A \/ B <-> B \/ A.
Proof.
(* Оскільки логічна еквівалентність є кон'юнкцією двох імплікацій, розглянемо
   кожну з цих імплікацій *)
  split.
  - (* у вирадку першої з цих імплікацій припустимо, що її антицендент є 
       вірним *)
    intro.
    (* розглянемо окремо припущення про справедливість кожного з диз'юнктів 
       гіпотези H *)
    destruct H as [H | H].
    + (* якщо вірним є лівий диз'юнкт, то він підтверджує правий диз'юнкт 
         цілі *) 
      right. assumption.
    + (* якщо ж вірним є правий диз'юнкт, то він підтверджує лівий диз'юнкт
         цілі*)
      left. assumption.
  - (* у вирадку другої з цих імплікацій припустимо, що її антицендент є 
       вірним *) 
    intro.
    (* розглянемо окремо припущення про справедливість кожного з диз'юнктів 
       гіпотези H *)
    destruct H as [H | H].
    + (* якщо вірним є правий диз'юнкт, то він підтверджує правий диз'юнкт 
         цілі *)
      right. assumption.
    + (* якщо ж вірним є лівий диз'юнкт, то він підтверджує лівий диз'юнкт
         ціді*)
      left. assumption.
Qed.

Lemma or_assoc: (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split; intro.
  - destruct H as [H | H]; try destruct H as [H | H].
    + left. assumption.
    + right. left. assumption.
    + right. right. assumption.
  - destruct H as [H | H]; try destruct H as [H | H].
    + left. left. assumption.
    + left. right. assumption.
    + right. assumption.
Qed.

Lemma or_assoc': (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split; intro; destruct H as [H | H]; try destruct H as [H | H];
  (left; assumption) || (right; assumption) || idtac;
  (left; left; assumption) || (left; right; assumption) ||
  (right; left; assumption) || (right; right; assumption).
Qed.

End orProperties.

Check or_comm.
Check or_assoc.


Section PLaxioms.
Variables A B C : Prop.

Lemma ax1 : A -> B -> A.  (* замінити Admitted на Proof. <доведення> Qed. *)
Admitted.
Check ax1.
Print ax1.

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
