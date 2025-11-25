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


Class Comparable
  (X : Set) 
  (cmp : X -> X -> comparison) : Prop := 
{
  cmp1 : forall x y, cmp x y = Eq <-> x = y
; cmp2 : forall x y, cmp x y = Gt <-> cmp y x = Lt
; cmp3 : forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt
}.

Section ComparableFacts.
Variable X : Set.
Variable cmp : X -> X -> comparison.
Context `{HComparable : Comparable X cmp}.

Let HCmp1 := @cmp1 X cmp HComparable.
Let HCmp2 := @cmp2 X cmp HComparable.
Let HCmp3 := @cmp3 X cmp HComparable.

Definition lt: X -> X -> Prop := fun x y => cmp x y = Lt.
Definition le: X -> X -> Prop := fun x y => lt x y \/ x = y.

Lemma lt_irrefl: forall x: X, ~ lt x x.
Proof.
  intros * H.
  assert (H1: cmp x x = Eq). { apply HCmp1. reflexivity. }
  (* unfold lt in H. *) rewrite H in H1. discriminate H1.
Qed.

Lemma lt_trans: forall x y z: X, lt x y -> lt y z -> lt x z.
Proof.
  intros * H1 H2. apply HCmp3 with y; assumption.
Qed. 

Definition lt_eq_lt_dec (x y : X) : {lt x y} + {x = y} + {lt y x}.
Proof.
  destruct (cmp x y) eqn: V.
  - left. right. apply HCmp1. assumption.
  - left. left. assumption.
  - right. apply HCmp2. assumption.
Defined.

Definition eq_dec (x y : X) : {x = y} + {x <> y}.
Proof.
  destruct (lt_eq_lt_dec x y) as [H | H].
  2: { right. intro. rewrite H0 in H. apply lt_irrefl with y. assumption. }
  destruct H as [H | H].
  2: { left. assumption. }
  right. intro. rewrite H0 in H. apply lt_irrefl with y. assumption.
Defined.

Definition le_gt_dec (x y : X) : {le x y} + {lt y x}.
Proof.
  destruct (lt_eq_lt_dec x y) as [H | H].
  2: { right. assumption. }
  destruct H as [H | H].
  - left. left. assumption.
  - left. right. assumption.
Defined.


Inductive sorted : list X -> Prop :=
  | sort0 : sorted []
  | sort1 : forall x, sorted [x]
  | sortS : forall x y lst, 
      le x y -> sorted (y :: lst) -> sorted (x :: y :: lst).

Fixpoint occnum (x : X) (lst : list X) : nat :=
  match lst with
  | [] => 0
  | y :: lst' => let k:= occnum x lst' in if (eq_dec x y) then S k else k
  end.

Definition same (lst1 lst2 : list X) : Prop :=
  forall x, occnum x lst1 = occnum x lst2.

Lemma same_refl : forall lst, same lst lst.
Proof.
  intro. induction lst as [| x lst' IHlst']; unfold same; trivial.
Qed.

Lemma same_symmetry : forall lst1 lst2, same lst1 lst2 -> same lst2 lst1.
Proof.
  intros. unfold same in H |-*. intro. rewrite (H x). reflexivity.
Qed.

Lemma same_transitivity :
  forall lst1 lst2 lst3, same lst1 lst2 -> same lst2 lst3 -> same lst1 lst3.
Proof.
  intros *. unfold same. intros H1 H2 *.
  rewrite (H1 x). apply H2.
Qed.

Lemma same_cons:
  forall x lst1 lst2, same lst1 lst2 -> same (x :: lst1) (x :: lst2).
Proof.
  unfold same. intros x lst1 lst2 H1 y. simpl. rewrite H1. reflexivity.
Qed.

Lemma same_permutation: forall x y lst1 lst2,
  same lst1 lst2 -> same (x :: y :: lst1) (y :: x :: lst2).
Proof.
  unfold same. intros. simpl. rewrite (H x0).
  case (eq_dec x0 x); case (eq_dec x0 y); reflexivity.
Qed.

End ComparableFacts.

Arguments le_gt_dec {X} {cmp} {HComparable}.
Arguments sorted {X} {cmp}.
Arguments sort0 {X} {cmp}.
Arguments sort1 {X} {cmp}.
Arguments sortS {X} {cmp}.
Arguments occnum {X} {cmp} {HComparable}.
Arguments same {X} {cmp} {HComparable}.
Arguments same_refl {X} {cmp} {HComparable}.
Arguments same_symmetry {X} {cmp} {HComparable}.
Arguments same_transitivity {X} {cmp} {HComparable}.
Arguments same_cons {X} {cmp} {HComparable}.
Arguments same_permutation {X} {cmp} {HComparable}.

#[global]Hint Constructors sorted : sortHDB.
#[global]Hint Unfold same : sortHDB.
#[global]Hint Resolve
  same_refl same_symmetry same_transitivity
  same_cons same_permutation : sortHDB.


Section NatComparable.
Definition nat_cmp := fix self (n m : nat) {struct n} : comparison :=
  match n with
    0    => match m with 0 => Eq | _    => Lt end
  | S n' => match m with 0 => Gt | S m' => self n' m' end
  end.

Instance natComparable : Comparable nat nat_cmp.
Proof.
  constructor.
  - intro. induction x as [| x' IHx']; intro; split; intro.
    + simpl in H. destruct y as [| y']; trivial. discriminate H.
    + rewrite <- H. reflexivity.
    + simpl in H. destruct y as [| y']; try discriminate H.
      f_equal. apply IHx'. assumption.
    + simpl. destruct y as [| y']; try discriminate H. apply IHx'.
      injection H; trivial.
  - intro. induction x as [| x' IHx']; intro; split; intro;
    destruct y as [| y']; try discriminate H; try reflexivity;
    simpl in H |-*; apply IHx'; assumption.
  - intro. induction x as [| x' IHx']; intros * H1 H2.
    + destruct z as [| z'].
      2: { simpl. reflexivity. }
      destruct y as [| y']; try discriminate H1.
      simpl in H2. discriminate H2.
    + destruct y as [| y']; try discriminate H1. simpl in H1.
      destruct z as [| z']; try discriminate H2. simpl in H2 |-*.
      apply (IHx' y' z'); trivial.
Defined.
End NatComparable.


Section InsertSort.
Variable X : Set.
Variable cmp : X -> X -> comparison.
Context `{HComparable : Comparable X cmp}.

Let HCmp1 := @cmp1 X cmp HComparable.
Let HCmp2 := @cmp2 X cmp HComparable.
Let HCmp3 := @cmp3 X cmp HComparable.

Fixpoint aux_ins_sort (x : X) (lst : list X) : list X :=
  match lst with
  | []        => [x]
  | y :: lst' => if (le_gt_dec x y)
                 then x :: y :: lst'
                 else y :: (aux_ins_sort x lst')
  end. 

Lemma aux_ins_sort_same : forall x lst, same (aux_ins_sort x lst) (x :: lst).
(* вставка у список в голову і за допомогою функції 'aux_ins_sort'
   дають схожі списки                                                         *)
Proof.
  intros. revert x.
  induction lst as [| y lst' IHlst'].
  - auto with sortHDB.
  - intro. pose (H1:= IHlst' x).
    simpl. destruct (le_gt_dec x y) as [H | H].
    + auto with sortHDB.
    + assert (same (y :: x :: lst') (x :: y :: lst')). { auto with sortHDB. }
      assert (same (y :: aux_ins_sort x lst') (y :: x :: lst')). {
        auto with sortHDB. }
      now apply same_transitivity with (y :: x :: lst').
Qed.

Lemma aux_ins_sort_inv :
  forall x lst, @sorted _ cmp lst -> @sorted _ cmp (aux_ins_sort x lst).
  (* функція 'aux_ins_sort' зберігає відсортованість списку                 *)
Proof.
  intros. elim H; simpl. 
  - auto with sortHDB.
  - intro y.
    destruct (le_gt_dec x y) as [H1 | H1]; constructor;
    assumption || constructor. assumption.
  - intros y z lst' H1 H2 H3.
    destruct (le_gt_dec x y) as [H0 | H0]; simpl.
    + constructor; try assumption. constructor; assumption.
    + destruct (le_gt_dec x z) as [H4 | H4]; auto with sortHDB.
      constructor; try assumption. left. assumption.
Qed.

Fixpoint ins_sort (lst : list X) : list X :=
(* функція сортування вставкою                                              *)
  match lst with
  | [] => []
  | n :: lst' => aux_ins_sort n (ins_sort lst')
  end.

Definition Correctness (f : list X -> list X) : Prop := 
  forall lst : list X, same lst (f lst) /\ @sorted _ cmp (f lst).

Theorem ins_sort_certified : Correctness ins_sort.
(* сертифікована функція сортування вставкою                                *)
Proof.
  intro. split.
  - induction lst as [| y lst' IHlst'].
    + auto with sortHDB.
    + simpl.
      assert (same (y :: lst') (y :: (ins_sort lst'))). { auto with sortHDB. }
      assert (same (aux_ins_sort y (ins_sort lst')) (y :: (ins_sort lst'))). {
        apply aux_ins_sort_same. }
      apply same_symmetry in H0.
      apply same_transitivity with (y :: ins_sort lst'); assumption.
  - induction lst as [| x lst' IHlst'].
    + constructor.
    + simpl. apply aux_ins_sort_inv. assumption.
Qed.
End InsertSort.


