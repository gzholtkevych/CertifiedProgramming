Require Import Lists.List.
Import ListNotations.

Locate comparison.
Check comparison.
Print comparison.

Module Type CMP.

  Parameter X : Set.
  Parameter cmp : X -> X -> comparison.

  Axiom cmp1 : forall x y, cmp x y = Eq <-> x = y.
  Axiom cmp2 : forall x y, cmp x y = Lt <-> cmp y x = Gt.
  Axiom cmp3 : forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.

End CMP.


Module Type TSO.

  Parameter X : Set.
  Parameter lt : X -> X -> Prop.

  Axiom lt_irrefl : forall x, ~ lt x x.
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

  Parameter lt_eq_gt_dec : forall x y, {lt x y} + {x = y} + {lt y x}.

End TSO.


Module toTSO (M : CMP) <: TSO with Definition X := M.X.
(* ------------------------ Setting parameters ------------------------------ *)
  Definition X := M.X.
  Definition lt := fun x y => M.cmp x y = Lt.

(* ------------------ Checking Signature Constraints ------------------------ *)
  Lemma lt_irrefl : forall x, ~ lt x x.
  Proof.
    intros * H. unfold lt in H.
    assert (x = x). { reflexivity. }
    pose (H1 := (proj2 (M.cmp1 x x)) H0).
    rewrite H1 in H. discriminate H.
  Qed.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. exact M.cmp3.
  Qed.

(* --------------------- Defining lt_eq_lt_dec ------------------------------ *)
  Definition lt_eq_gt_dec (x y : X) : {lt x y} + {x = y} + {lt y x}.
  Proof.
    destruct (M.cmp x y) eqn : V.
    - left. right. apply M.cmp1. assumption.
    - left. left. assumption.
    - right. apply M.cmp2. assumption.
  Defined.

(* ----------------- Additional Definitions and Facts ----------------------- *)
  Definition eq_dec (x y : X) : {x = y} + {x <> y}.
  Proof.
    destruct (M.cmp x y) eqn: V.
    - left. apply M.cmp1. assumption.
    - right. intro. rewrite H in V. assert (y = y). { reflexivity. }
      pose (H1 := (proj2 (M.cmp1 y y)) H0). rewrite H1 in V. discriminate V.
    - right. intro. rewrite H in V. assert (y = y). { reflexivity. }
      pose (H1 := (proj2 (M.cmp1 y y)) H0). rewrite H1 in V. discriminate V.
  Defined.

  Definition le (x y : X) := lt x y \/ x = y.
  Definition le_gt_dec (x y : X) : {le x y} + {lt y x}.
  Proof.
    unfold le.
    destruct (lt_eq_gt_dec x y) as [HLe | HGt]; try destruct HLe as [HLt | HEq].
    - now repeat left.
    - left. now right.
    - now right.
  Defined.

End toTSO.


Module Type SORT.
  Parameter X : Set.
  Parameter lt : X -> X -> Prop.
  Parameter lt_eq_gt_dec : forall x y : X, {lt x y} + {x = y} + {lt y x}.
  Parameter sorted : list X -> Prop.
  Parameter same : list X -> list X -> Prop.
End SORT.


Module toSORT (M : CMP) <: SORT with Definition X := M.X.

  Definition X := M.X.
  Module MTSO := toTSO(M).

  Definition lt := MTSO.lt.
  Definition lt_eq_gt_dec := MTSO.lt_eq_gt_dec.
  Definition le := MTSO.le.
  Definition eq_dec := MTSO.eq_dec.
  Definition le_gt_dec := MTSO.le_gt_dec.

  Inductive sorted' : list X -> Prop :=
    | sort0 : (* порожній список є відсортованим                              *)
        sorted' []
    | sort1 : (* будь-який одноелементний список є відсортованим              *)
        forall x, sorted' [x]
    | sortS : (* якщо в голову відсортованого списку додати число меше або рівне
                 першому елементу списку, то отримаємо відсортований список   *)
        forall x y lst,
          le x y -> sorted' (y :: lst) -> sorted' (x :: y :: lst).
  Definition sorted := sorted'.

  #[global] Hint Resolve sort0 sort1 sortS : sortHDB.

  Fixpoint occnum (x : X) (lst : list X) : nat :=
    (* кількість входжень 'x' в список lst                                    *)
    match lst with
    | [] => 0
    | y :: lst' => if eq_dec x y then S (occnum x lst') else occnum x lst'
    end.

  Definition same : list X -> list X -> Prop :=
    (* визначення списків однакових за складом, які будемо називати схожими   *)
    fun lst' lst'' => forall x, occnum x lst' = occnum x lst''.

  #[global] Hint Unfold same : sortHDB.

  Section SameProperties.
  Variables (lst1 lst2 lst3 : list X) (x y : X).

    Lemma same_reflexivity : same lst1 lst1.
    Proof. auto with sortHDB. Qed.

    Lemma same_symmetry : same lst1 lst2 -> same lst2 lst1.
    Proof. auto with sortHDB. Qed.

    Lemma same_transitivity :
      same lst1 lst2 -> same lst2 lst3 -> same lst1 lst3.
    Proof. unfold same. intros. rewrite H. apply H0. Qed.
    (* тобто відношенням схожесті є еквівалентністю на спиках                 *)

    Lemma same_cons : same lst1 lst2 -> same (x :: lst1) (x :: lst2).
    (* якщо в голови схожих списків вставити одне й те саме число,
       то отримаємо схожі списки                                              *)
    Proof. unfold same. intros. simpl. rewrite H. reflexivity. Qed.

    Lemma same_permutation : 
      same lst1 lst2 -> same (x :: y :: lst1) (y :: x :: lst2).
    (* якщо в голови схожих списків додати в різному порядку одні й ті самі 
       два числа у кожний то отримаємо схожі списки                           *)
    Proof.
      unfold same. intros. simpl. rewrite H.
      case (eq_dec x0 y); case (eq_dec x0 x); reflexivity.
    Qed.
  End SameProperties.

  #[global] Hint Resolve
    same_reflexivity same_symmetry same_transitivity 
    same_cons same_permutation : sortHDB.

  Definition Correctness (f : list X -> list X) : Prop := 
    forall lst : list X, same lst (f lst) /\ sorted (f lst).

End toSORT.


Module InsertionSort (M : CMP).
  Module MSORT := toSORT(M).
  Import MSORT.

  Fixpoint aux_ins_sort (x : X) (lst : list X) : list X :=
    (* вставляє 'x' у список перед першим елементом списку,
       що не менший за 'x'                                                    *)
    match lst with
    | [] => [x]
    | y :: lst' => if le_gt_dec x y then x :: y :: lst'
                   else y :: (aux_ins_sort x lst')
    end.

  Lemma aux_ins_sort_same : forall x lst, same (aux_ins_sort x lst) (x :: lst).
  (* вставка у список в голову і за допомогою функції 'aux_ins_sort'
     дають схожі списки                                                       *)
  Proof.
    intros. revert x.
    induction lst as [| y lst' IHlst'].
    - auto with sortHDB.
    - intros x z. simpl aux_ins_sort.
      destruct (le_gt_dec x y).
      + reflexivity.
      + assert (occnum z (x :: y :: lst') = occnum z (y :: x :: lst')). {
          rewrite same_permutation with lst' lst' _ _ _; auto with sortHDB. }
        rewrite H. now apply same_cons.
  Qed.

  Lemma aux_ins_sort_inv :
    forall x lst, sorted lst -> sorted (aux_ins_sort x lst).
    (* функція 'aux_ins_sort' зберігає відсортованість списку                 *)
  Proof.
    intros. elim H; simpl. auto with sortHDB; try constructor.
    - intro y. case (le_gt_dec x y); constructor;
      assumption || constructor || unfold le. assumption.
    - intros y z lst' H1 H2 H3.
      destruct (le_gt_dec x y); simpl.
      + constructor; [ assumption | now constructor ].
      + destruct (le_gt_dec x z); auto with sortHDB.
        constructor; try assumption; compute; now left. now constructor.
  Qed.

  Fixpoint ins_sort (lst : list X) : list X :=
  (* функція сортування вставкою                                              *)
    match lst with
    | [] => []
    | n :: lst' => aux_ins_sort n (ins_sort lst')
    end.

  Theorem ins_sort_certified : Correctness ins_sort.
  (* сертифікована функція сортування вставкою                                *)
  Proof.
    intro. split.
    - unfold same. intro.
      induction lst as [| y lst' IHlst'].
      + reflexivity.
      + simpl. destruct (eq_dec x y).
        * assert (same (aux_ins_sort y (ins_sort lst')) (y :: (ins_sort lst'))). 
          { apply aux_ins_sort_same. }
          rewrite H. rewrite <- e. simpl.
          destruct (eq_dec x x); try contradiction.
            rewrite IHlst'; reflexivity.
        * simpl. destruct (eq_dec x y); try contradiction.
          rewrite IHlst'.
          assert (same (aux_ins_sort y (ins_sort lst')) ( y :: ins_sort lst')).
          { apply aux_ins_sort_same. }
          rewrite H. simpl. destruct (eq_dec x y). try contradiction.
          reflexivity.
    - induction lst as [| x lst' IHlst'].
      + constructor.
      + simpl. now apply aux_ins_sort_inv.
  Qed.
End InsertionSort.


(* ----------------------- Випадок натуральних чисел ------------------------ *)
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.

Module CMPNat <: CMP.

  Definition X := nat.
  Definition cmp (x y : X) : comparison :=
    match lt_eq_lt_dec x y with
    | inleft HLe => match HLe with
                   | left _  => Lt
                   | right _ => Eq
                   end
    | inright _ => Gt
    end.

  Lemma cmp1 : forall x y : X, cmp x y = Eq <-> x = y.
  Proof.
    intros. unfold cmp.
    destruct (lt_eq_lt_dec x y) as [HLe | HGt];
    try destruct HLe as [HLt | HEq].
    - split; intro; try discriminate H. rewrite H in HLt.
      exfalso. now apply Nat.lt_irrefl with y.
    - split; intro; assumption || reflexivity.
    - split; intro; try discriminate H. rewrite H in HGt.
      exfalso. now apply Nat.lt_irrefl with y.
  Qed.

  Lemma cmp2 : forall x y : X, cmp x y = Lt <-> cmp y x = Gt.
  Proof.
    intros. unfold cmp.
    destruct (lt_eq_lt_dec x y) as [HLe | HGt];
    try destruct HLe as [HLt | HEq].
    - split; intro.
      + destruct (lt_eq_lt_dec y x) as [HLe | HGt];
        try destruct HLe as [HLt' | HEq].
        * exfalso. apply Nat.lt_irrefl with y. now apply Nat.lt_trans with x.
        * rewrite HEq in HLt. exfalso. now apply Nat.lt_irrefl with x.
        * reflexivity.
      + reflexivity.
    - split; intro.
      + destruct (lt_eq_lt_dec x y) as [HLe | HGt];
        try destruct HLe as [HLt | HEq].
        * discriminate H.
        * destruct (lt_eq_lt_dec y x) as [HLe | HGt'];
          try destruct HLe as [HLt | HEq']; discriminate H.
      + rewrite HEq in H.
        destruct (lt_eq_lt_dec y y) as [HLe | HGt];
        try destruct HLe as [HLt | HEq']; try discriminate H.
        exfalso. now apply Nat.lt_irrefl with y.
    - split; intro.
      + discriminate H.
      + destruct (lt_eq_lt_dec y x) as [HLe | HGt'];
        try destruct HLe as [HLt | HEq]; try discriminate H.
        exfalso. apply Nat.lt_irrefl with y. now apply Nat.lt_trans with x.
  Qed.

  Lemma cmp3 : forall x y z : X, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.
  Proof.
    intros * H1 H2. unfold cmp in H1, H2 |-*.
    destruct (lt_eq_lt_dec x y) as [HLe | HGt];
    try destruct HLe as [HLt | HEq]; try discriminate H1.
    destruct (lt_eq_lt_dec y z) as [HLe | HGt];
    try destruct HLe as [HLt' | HEq]; try discriminate H2.
    destruct (lt_eq_lt_dec x z) as [HLe | HGt];
    try destruct HLe as [HLt'' | HEq].
    - reflexivity.
    - rewrite HEq in HLt.
      exfalso. apply Nat.lt_irrefl with y. now apply Nat.lt_trans with z.
    - assert (x < z). { now apply Nat.lt_trans with y. }
      exfalso. apply Nat.lt_irrefl with x. now apply Nat.lt_trans with z.
  Qed.
End CMPNat.


Module NatInsertionSort := InsertionSort(CMPNat).
Import NatInsertionSort.

Eval simpl in ins_sort [5; 4; 3; 2; 1].


(* ---------------------- Випадок цілих чисел (тип Z) ----------------------- *)
(* наведіть відповідний текст, аналогічний випадку натуральних чисел тут      *)

