(* Тріада: терм - тип - сорт, де сорт є або Set, або Prop, або Type.
   Все є терми, деякі з термів є типами.
   Сорти - це спеціальні типові константи Set, Prop та Type.
   Сорт Type насправді індексований натуральними числами
      Type_1, ..., Type_k, ..., але індекс завжди прихований.
   Кожний терм t населяє певний тип T, що позначається через t : T.
   Наприклад, Prop : Set, Set : Type_1, Type_k : Type_{k+1}.
   Наспроавді постулюється справедливість таких суджень:
      Prop : Set
      Set : Type_1
      Type_n : Type_m, якщо n < m
*)

Check Set.
Check Prop.
Check Type.

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

Locate and.
Check and.
Print Term and.
Check and_ind.

Section andProperties.
Variables A B C : Prop.

Lemma and_comm : A /\ B <-> B /\ A.
Proof.
  split; intro.
  - destruct H as (HA, HB).
    (* pose (HBA := conj HB HA). exact HBA. *)
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
  - elim H. intros. elim H0. intros; repeat split; assumption.
  - elim H. intros. elim H1. intros; repeat split; assumption.
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

Locate or.
Check or.
Print Term or.
Check or_ind.

Section orProperties.
Variables A B C : Prop.

Lemma or_comm : A \/ B <-> B \/ A.
Proof.
(* Оскільки логічна еквівалентність є кон'юнкцією двох імплікацій, розглянемо
   кожну з цих імплікацій *)
  split.
  - (* у вирадку першої з цих імплікацій припустимо, що її антицендкнт є 
       вірним *)
    intro.
    (* розглянемо окремо припущення про справедливість кожного з диз'юнктів 
       гіпотези H *)
    destruct H as [HA | HB].
    + (* якщо вірним є лівий диз'юнкт, то він підтверджує правий диз'юнкт 
         цілі *) 
      right. assumption.
    + (* якщо ж вірним є правий диз'юнкт, то він підтверджує лівий диз'юнкт
         ціді*)
      left. assumption.
  - (* у вирадку першої з цих імплікацій припустимо, що її антицендкнт є 
       вірним *) 
    intro.
    (* розглянемо окремо припущення про справедливість кожного з диз'юнктів 
       гіпотези H *)
    destruct H as [HB | HA].
    + (* якщо вірним є правий диз'юнкт, то він підтверджує правий диз'юнкт 
         цілі *)
      right. assumption.
    + (* якщо ж вірним є лівий диз'юнкт, то він підтверджує лівий диз'юнкт
         ціді*)
      left. assumption.
Qed.

Lemma or_assoc: (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split.
  - intro.
    elim H.
    + intro.
      elim H0.
      * intro. left. assumption.
      * intro. right. left. assumption.
    + intro. right. right. assumption.
  - intro.
    elim H.
    + intro.
      left. left. assumption.
    + intro.
      elim H0.
      * intro. left. right. assumption.
      * intro. right. assumption.
Qed.

End orProperties.

Print Term or_comm.
Print Term or_assoc.


Section PLaxioms.
Variables A B C : Prop.

Lemma ax1 : A -> B -> A.
Admitted.  (* замінити Admitted на Proof. <доведення> Qed                     *)
Check ax1.
Print ax1.

Lemma ax2 : (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  intros H1 H2 H3. apply H2.
  - assumption.
(*  - apply H1. assumption. *)
  - pose (H := H1 H3). assumption.
Qed.

Lemma ax3 : A /\ B -> A.
Admitted.

Lemma ax4 : A /\ B -> B.
Admitted.

Lemma ax5 : (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
  intros H1 H2 H3. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax6 : A -> A \/ B.
Admitted.

Lemma ax7 : B -> A \/ B.
Admitted.

Lemma ax8 : (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros H1 H2 H3.
  elim H3; intro H.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma ax9 : (A -> ~ B) -> B -> ~ A.
Admitted.

End PLaxioms.
