(* Теорія алгоритмів сортування                                               
   --------------------------------------------------------------------------
   Об'єктом сортування є списки з елементами певного типу.
   Для елементів списків має бути визначений інструмент порівняння, який
   забезпечуює наявність лінійного порядку.

   Задача сортуання полягає у побудові функції над списками, яка
   1) дає сортований список як результат
   2) цнй результуючий список має складатися з тих самих елементів.
  --------------------------------------------------------------------------- *)
Require Import Lists.List.
Import ListNotations.

Print comparison.


Module Type CMP_CORE.
  (* Специфікація даних, що відповідають задачі сортування                    *)

  Parameter data : Set.                        (* дані, що сортуються         *)

  Parameter cmp : data -> data -> comparison.  (* інструмент порівняння       *)

  (* Вимоги до інструмента порівняння                                         *)
  Axiom cmp_diag : forall x y : data, cmp x y = Eq <-> x = y.

  Axiom cmp_asym : forall x y : data, cmp x y = Lt <-> cmp y x = Gt.

  Axiom cmp_trns : forall (c : comparison) (x y z : data),
    cmp x y = c -> cmp y z = c -> cmp x z = c.

End CMP_CORE.


Module NatCMP_CORE : CMP_CORE.
  (* Реалізація специфікації для типу натуральних чисел                       *)

  Definition data := nat.

  Definition cmp := fix cmp_nat (x y : data) :=
    match x, y with
      0, 0 => Eq |
      0, S y' => Lt |
      S x', 0 => Gt |
      S x', S y' => cmp_nat x' y'
    end.

  Lemma cmp_diag : forall x y : data, cmp x y = Eq <-> x = y.
  Proof.
    induction x; intro; split; intro; destruct y; trivial || idtac;
      simpl; simpl in H; discriminate || idtac; apply (IHx y) || idtac.
    - assert (H1 : x = y). { now apply IHx. }
      now rewrite H1.
    - now injection H.
  Qed.

  Lemma cmp_asym : forall x y : data, cmp x y = Lt <-> cmp y x = Gt.
  Proof.
    induction x; intro; split; intro; destruct y; trivial || idtac;
      discriminate H || idtac; simpl in H; simpl; now apply IHx.
  Qed.

  Lemma cmp_trns :  forall (c : comparison) (x y z : data),
    cmp x y = c -> cmp y z = c -> cmp x z = c.
  Proof.
    intro. induction x; intros; destruct c; destruct z; trivial || idtac;
      destruct y; simpl in H; trivial; simpl; discriminate || idtac;
      now apply (IHx y z).
  Qed.

End NatCMP_CORE.


Module Type CMP_ORDER.

  Parameter data : Set.

  Parameter cmp : data -> data -> comparison.

  Axiom cmp_diag : forall x y : data, cmp x y = Eq <-> x = y.

  Axiom cmp_asym : forall x y : data, cmp x y = Lt <-> cmp y x = Gt.

  Axiom cmp_trns : forall (c : comparison) (x y z : data),
    cmp x y = c -> cmp y z = c -> cmp x z = c.

  Parameter ltCmp : data -> data -> Prop.

  Parameter leCmp : data -> data -> Prop.

  Axiom le_def : forall x y : data, leCmp x y <-> x = y \/ ltCmp x y.

  Axiom lt_irrf : forall x : data, ~ ltCmp x x.

  Axiom lt_trns : forall x y z : data, ltCmp x y -> ltCmp y z -> ltCmp x z.

  Parameter lt_dec : forall x y : data, {ltCmp x y} + {x = y} + {ltCmp y x}.

  Parameter sorted : list data -> Prop.

  Axiom eq_dec : forall x y : data, {x = y} + {x <> y}.
(*
  Parameter same : list data -> list data -> Prop.

  Axiom same_rfl : forall xs : list data, same xs xs.

  Axiom same_sym : forall xs ys : list data, same xs ys -> same ys xs.

  Axiom same_trn : forall xs ys zs : list data,
    same xs ys -> same ys zs -> same xs zs.
*)
End CMP_ORDER.


Module TO_CMP_ORDER (M : CMP_CORE) : CMP_ORDER
  with Definition data := M.data 
  with Definition ltCmp := fun x y => M.cmp x y = Lt.

  Definition data := M.data.

  Definition cmp := M.cmp.  

  Definition ltCmp := fun x y => M.cmp x y = Lt.

  Definition leCmp := fun x y => ltCmp x y \/ x = y.

  Lemma le_def : forall x y : data, leCmp x y <-> x = y \/ ltCmp x y.
  Proof.
    intros. split; intro; elim H; intro H'; try now right.
    - now left.
    - now left.
  Qed.

  Lemma cmp_diag : forall x y : data, cmp x y = Eq <-> x = y.
  Proof. exact M.cmp_diag. Qed.

  Lemma cmp_asym : forall x y : data, cmp x y = Lt <-> cmp y x = Gt.
  Proof. exact M.cmp_asym. Qed.

  Lemma cmp_trns : forall (c : comparison) (x y z : data),
    cmp x y = c -> cmp y z = c -> cmp x z = c.
  Proof. exact M.cmp_trns. Qed.

  Lemma lt_irrf : forall x : data, ~ ltCmp x x.
  Proof.
    unfold ltCmp. intros * H.
    pose (H1 := proj2 (M.cmp_diag x x)).
    assert (H2 : x = x). { trivial. }
    pose (H' := H1 H2). rewrite H' in H. discriminate H.
  Qed.

  Lemma lt_trns : forall x y z : data, ltCmp x y -> ltCmp y z -> ltCmp x z.
  Proof. unfold ltCmp. exact (M.cmp_trns Lt). Qed.

  Definition lt_dec : forall x y : data, {ltCmp x y} + {x = y} + {ltCmp y x}.
  Proof.
    unfold ltCmp. intros.
    elim M.cmp_diag with x y. intros HD1 HD2.
    elim M.cmp_asym with y x. intros HA1 HA2.
    assert (H : {M.cmp x y = Eq} + {M.cmp x y = Lt} + {M.cmp x y = Gt}). {
      destruct (M.cmp x y); [left | left | right]; trivial || idtac;
      [left | right]; trivial. }
    elim H; intro H1; elim H1; intro H2 || idtac.
    - pose (H3 := HD1 H2). left. now right.
    - left. now left.
    - assert (H2 : M.cmp y x = Lt). { now apply HA2. }
      now right.
  Defined.

  Inductive sorted' : list data -> Prop :=
    sorted_0 : sorted' [] |
    sorted_1 : forall x : data, sorted' [x] |
    sorted_other : forall (x y : data) (ls : list data),
      leCmp x y -> sorted' (y :: ls) -> sorted' (x :: y :: ls).
  Definition sorted := sorted'.

  Lemma eq_dec : forall x y : data, {x = y} + {x <> y}.
  Proof.
    intros. elim (lt_dec x y); intro H; try elim H; try intro H'.
    - right. intro. rewrite H0 in H'. revert H'. exact (lt_irrf y).
    - now left.
    - right. intro. rewrite H0 in H. revert H. exact (lt_irrf y).
  Qed.
(*
  Definition same (xs ys : list data) : Prop :=
    forall x : data, count_occ eq_dec xs x = count_occ eq_dec ys x. 
*)
End TO_CMP_ORDER.


Module NatCMP_ORDER := TO_CMP_ORDER NatCMP_CORE.

Check NatCMP_ORDER.lt_dec.

