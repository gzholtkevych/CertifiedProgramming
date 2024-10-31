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

Definition eq_dec (x y : X) : {x = y} + {x <> y}.
Proof.
  assert (HEL : forall x : X, x = x). { trivial. }
  destruct (cmp x y) eqn: HV; try (left; apply HCmp1; assumption);
  right; intro HE; rewrite HE in HV; pose (HV' := proj2 (HCmp1 y y) (HEL y));
  rewrite HV' in HV; discriminate HV.
Defined.

Definition lt : X -> X -> Prop := fun x y => cmp x y = Lt.
Definition le : X -> X -> Prop := fun x y => lt x y \/ x = y.

Definition le_gt_dec (x y : X) : {le x y} + {lt y x}.
Proof.
  destruct (cmp x y) eqn: HV.
  - left. right. apply HCmp1. assumption.
  - left. left. assumption.
  - right. apply HCmp2. assumption.
Defined.

Inductive sorted : list X -> Prop :=
  | sort0 : sorted []
  | sort1 : forall x, sorted [x]
  | sortS : forall x y lst, 
      le x y -> sorted (y :: lst) -> sorted (x :: y :: lst).

Fixpoint occnum (x : X) (lst : list X) : nat :=
  match lst with
  | [] => 0
  | y :: lst' => if (eq_dec x y)
                 then S (occnum x lst')
                 else (occnum x lst')
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

Lemma same_ins :
  forall x lst1 lst2, same lst1 lst2 -> same (x :: lst1) (x :: lst2).
Proof.
  unfold same. intros x lst1 lst2 H1 y. simpl. rewrite H1. reflexivity.
Qed.

Lemma same_permute : forall x y lst1 lst2,
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
Arguments same_ins {X} {cmp} {HComparable}.
Arguments same_permute {X} {cmp} {HComparable}.

Check sorted.

#[export]Hint Constructors sorted : sortHDB.
#[export]Hint Unfold same : sortHDB.
#[export]Hint Resolve
  same_refl same_symmetry same_transitivity same_ins same_permute : sortHDB.



Section NatComparable.
Definition nat_cmp := fix cmp (n m : nat) {struct n} : comparison :=
  match n with
    0    => match m with 0 => Eq | _    => Lt end
  | S n' => match m with 0 => Gt | S m' => cmp n' m' end
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
  - intro. induction x as [| x' IHx']; intro; split; intro H1;
    destruct y as [| y']; try discriminate H1; try reflexivity;
    simpl in H1 |-*; apply IHx'; assumption.
  - intro.
    induction x as [| x' IHx']; intros * H1 H2.
    + destruct y as [| y']; try discriminate H1.
      destruct z as [| z']; discriminate H2 || reflexivity.
    + destruct y as [| y']; try discriminate H1.
      simpl in H1. destruct z as [| z']; try discriminate H2.
      simpl in H2 |-*. apply (IHx' y' z'); trivial.
Defined.
End NatComparable.


Section InsertSort.
Variable X : Set.
Variable cmp : X -> X -> comparison.
Context `{HComparable : Comparable X cmp}.

Let HCmp1 := @cmp1 X cmp HComparable.
Let HCmp2 := @cmp2 X cmp HComparable.
Let HCmp3 := @cmp3 X cmp HComparable.

Fixpoint aux_ins (x : X) (lst : list X) : list X :=
  match lst with
  | []        => []
  | y :: lst' => if (le_gt_dec x y)
                 then x :: y :: lst'
                 else y :: (aux_ins x lst')
  end. 

Lemma aux_ins_sorted :
  forall x (lst : list X), @sorted _ cmp lst -> @sorted _ cmp (aux_ins x lst).
Proof.

End InsertSort.
