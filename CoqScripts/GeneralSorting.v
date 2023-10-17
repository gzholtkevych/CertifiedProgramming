Require Import Lists.List.
Import ListNotations.


Module Type Comparable.
  Parameter X : Set.
  Parameter cmp : X -> X -> comparison.
  
  Axiom cmp1 : forall x y, cmp x y = Eq <-> x = y.
  Axiom cmp2 : forall x y, cmp x y = Lt <-> cmp y x = Gt.
  Axiom cmp3 : forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.
End Comparable.

Module Type TotalStrongOrdered.
  Parameter X : Set.
  Parameter lt : X -> X -> Prop.
  Parameter lt_eq_lt_dec : forall x y, {lt x y} + {x = y} + {lt y x}.
  
  Axiom lt_irrefl : forall x, ~ lt x x.
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
End TotalStrongOrdered.

Module Comparable_to_TotalStrongOrdered (C : Comparable) <: TotalStrongOrdered.
Include C.
(* ------------------ Checking Signature Constraints ------------------------ *)
  Definition lt := fun x y => cmp x y = Lt.
  Definition lt_eq_lt_dec (x y : X) : {lt x y} + {x = y} + {lt y x}.
  Proof.
    destruct (cmp x y) eqn : V.
    - left. right. apply cmp1. assumption.
    - left. left. assumption.
    - right. apply cmp2. assumption.
  Defined.
  
  Lemma lt_irrefl : forall x, ~ lt x x.
  Proof.
    intros * H. unfold lt in H.
    assert (cmp x x = Eq). { apply cmp1. reflexivity. }
    rewrite H0 in H. discriminate H.
  Qed.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. exact cmp3.
  Qed.
(* ----------------- Additional Definitions and Facts ----------------------- *)
  Definition eq_dec (x y : X) : {x = y} + {x <> y}.
  Proof.
    destruct (lt_eq_lt_dec x y) as [HLe | HGt]; try destruct HLe as [HLt | HEq].
    - right. intro. rewrite H in HLt. now apply lt_irrefl with y.
    - now left.
    - right. intro. rewrite H in HGt. now apply lt_irrefl with y.
  Defined.

  Definition le (x y : X) := lt x y \/ x = y.
  Definition le_gt_dec (x y : X) : {le x y} + {lt y x}.
  Proof.
    unfold le.
    destruct (lt_eq_lt_dec x y) as [HLe | HGt]; try destruct HLe as [HLt | HEq].
    - now repeat left.
    - left. now right.
    - now right.
  Defined.

  Inductive sorted : list X -> Prop :=
    | sort0 : (* порожній список є відсортованим                              *)
        sorted []
    | sort1 : (* будь-який одноелементний список є відсортованим              *)
        forall x, sorted [x]
    | sortS : (* якщо в голову відсортованого списку додати число меше або рівне
                 першому елементу списку, то отримаємо відсортований список   *)
        forall x y lst,
          le x y -> sorted (y :: lst) -> sorted (x :: y :: lst).

  #[export] Hint Constructors sorted : sortHDB.

  Fixpoint occnum (x : X) (lst : list X) : nat :=
    (* кількість входжень 'x' в список lst                                    *)
    match lst with
    | [] => 0
    | y :: lst' => if eq_dec x y then S (occnum x lst') else occnum x lst'
    end.

  Definition same : list X -> list X -> Prop :=
    (* визначення списків однакових за складом, які будемо називати схожими   *)
    fun lst' lst'' => forall x, occnum x lst' = occnum x lst''.

  #[export] Hint Unfold same : sortHDB.

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

  #[export] Hint Resolve
    same_reflexivity same_symmetry same_transitivity 
    same_cons same_permutation : sortHDB.

  Definition CertifiedSortingAlgorithm :=
    (* алгоритм сортування є                                                  *)
    { f : list X -> list X  (* функцією, що перетворює список на список       *)
      | (forall lst, same lst (f lst)) /\  (* зберігає склад списку           *)
        (forall lst, sorted (f lst)) }.    (* та утворює відсортований список *)
End Comparable_to_TotalStrongOrdered.

Module InsertionSort (C : Comparable).
  Module COrd := Comparable_to_TotalStrongOrdered(C).
  Include COrd.

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
    intros. elim H; simpl; auto with sortHDB.
    - intro y. case (le_gt_dec x y); constructor;
      assumption || constructor || unfold le. assumption.
    - intros y z lst' H1 H2 H3.
      destruct (le_gt_dec x y); simpl.
      + auto with sortHDB.
      + destruct (le_gt_dec x z); auto with sortHDB.
        constructor; try assumption. unfold le. now left.
  Qed.

  Fixpoint ins_sort (lst : list X) : list X :=
  (* функція сортування вставкою                                              *)
    match lst with
    | [] => []
    | n :: lst' => aux_ins_sort n (ins_sort lst')
    end.

  Theorem ins_sort_certified : CertifiedSortingAlgorithm.
  (* сертифікована функція сортування вставкою                                *)
  Proof. 
    exists ins_sort.
    split; intro.
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
      + auto with sortHDB.
      + simpl. now apply aux_ins_sort_inv.
  Qed.
End InsertionSort.


Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.
Module Comparable_nat : Comparable.
  Definition X := nat.
  Definition cmp : X -> X -> comparison.
  Proof.
    intros n m.
    destruct (lt_eq_lt_dec n m) as [HLe | HGt]; try destruct HLe as [Hlt | Heq].
    - exact Lt.
    - exact Eq.
    - exact Gt.
  Defined.

  Lemma cmp1 : forall n m, cmp n m = Eq <-> n = m.
  Proof.
    intros. split; intro. unfold cmp in H.
    - destruct (lt_eq_lt_dec n m) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq]; discriminate H || assumption.
    - unfold cmp.
      destruct (lt_eq_lt_dec n m) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq]; try reflexivity;
      [ rewrite H in Hlt | rewrite H in Hgt ]; exfalso;
      now apply Nat.lt_irrefl with m.
  Qed.
    
  Lemma cmp2 : forall n m, cmp n m = Lt <-> cmp m n = Gt.
  Proof.
    intros. split; unfold cmp; intro;
    destruct (lt_eq_lt_dec n m) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq]; trivial; try discriminate H;
    try destruct (lt_eq_lt_dec m n) as [Hle' | Hgt'];
    try destruct Hle' as [Hlt' | Heq']; try discriminate H; try reflexivity.
    - assert (H1 : n < n). { now apply Nat.lt_trans with m. }
      exfalso. now apply Nat.lt_irrefl with n.
    - rewrite Heq' in Hlt. exfalso. now apply Nat.lt_irrefl with n.
    - rewrite Heq in Hgt'. exfalso. now apply Nat.lt_irrefl with m.
    - assert (H1 : n < n). { now apply Nat.lt_trans with m. }
      exfalso. now apply Nat.lt_irrefl with n.
  Qed.

  Lemma cmp3 : forall n m k, cmp n m = Lt -> cmp m k = Lt -> cmp n k = Lt.
  Proof.
    intros *. unfold cmp. intros H1 H2.
    destruct (lt_eq_lt_dec n k) as [Hle_n_k | Hgt_n_k];
    try destruct Hle_n_k as [Hlt_n_k | Heq_n_k]; try reflexivity;
    destruct (lt_eq_lt_dec n m) as [Hle_n_m | Hgt_n_m];
    try destruct Hle_n_m as [Hlt_n_m | Heq_n_m]; try discriminate H1;
    destruct (lt_eq_lt_dec m k) as [Hle_m_k | Hgt_m_k];
    try destruct Hle_m_k as [Hlt_m_k | Heq_m_k]; try discriminate H2;
    exfalso.
    - rewrite Heq_n_k in Hlt_n_m.
      assert (H3 : m < m). { now apply Nat.lt_trans with k. }
      now apply Nat.lt_irrefl with m.
    - assert (H3 : k < m). { now apply Nat.lt_trans with n. }
      assert (H4 : m < m). { now apply Nat.lt_trans with k. }
      now apply Nat.lt_irrefl with m.
  Qed. 

End Comparable_nat.

Module InsertionSort_nat := InsertionSort(Comparable_nat).
