Require Import Lists.List.
Import ListNotations.
Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.


Inductive sorted : list nat -> Prop :=
  | sort0 : (* порожній список є відсортованим                                *)
      sorted []
  | sort1 : (* будь-який одноелементний список є відсортованим                *)
      forall n, sorted [n]
  | sortS : (* якщо в голову відсортованого списку додати число меше
               за перший елемент списку, то отримаємо відсортований список    *)
      forall n m lst, 
        n <= m -> sorted (m :: lst) -> sorted (n :: m :: lst).

#[export] Hint Constructors sorted : sortHDB.

Example s12345 : sorted [1; 2; 3; 4; 5].
Proof.
(* Можна так:
  apply sortS. apply le_S. apply le_n.
  apply sortS. apply le_S. apply le_n.
  apply sortS. apply le_S. apply le_n.
  apply sortS. apply le_S. apply le_n.
  apply sort1.
Але оскільки ми застосовуємо тільки конструктори, то можна і так *)
 repeat constructor. Qed.

Fixpoint occnum (n : nat) (lst : list nat) : nat :=
  (* кількість входжень числа n в список lst                                  *)
  match lst with
  | [] => 0
  | m :: lst' => if Nat.eq_dec n m then S (occnum n lst') else occnum n lst'
  end.

Eval simpl in occnum 3 [].
Eval simpl in occnum 3 [1; 3; 2; 5; 3].

Definition same : list nat -> list nat -> Prop :=
  (* визначення списків однакових за складом, які будемо називати схожими     *)
  fun lst' lst'' => forall n, occnum n lst' = occnum n lst''.

#[export] Hint Unfold same : sortHDB.

Section SameProperties.
Variables (lst1 lst2 lst3 : list nat) (n m : nat).

  Lemma same_reflexivity : same lst1 lst1.
  Proof. auto with sortHDB. Qed.

  Lemma same_symmetry : same lst1 lst2 -> same lst2 lst1.
  Proof. auto with sortHDB. Qed.

  Lemma same_transitivity : same lst1 lst2 -> same lst2 lst3 -> same lst1 lst3.
  Proof. unfold same. intros. rewrite <- H0. exact (H n0). Qed.
  (* тобто відношенням схоєесті є еквівалентністю на спиках                   *)

  Lemma same_cons : same lst1 lst2 -> same (n :: lst1) (n :: lst2).
  (* якщо в голови схожих списків вставити одне й те саме число,
     то торимаємо схожі списки                                                *)
  Proof. unfold same. intros. simpl. rewrite H. reflexivity. Qed.

  Lemma same_permutation : 
    same lst1 lst2 -> same (n :: m :: lst1) (m :: n :: lst2).
  (* якщо в голови схожих списків додати в різному порядку одні й ті самі 
     два числа у кожний то отримаємо схожі списки                             *)
  Proof.
    unfold same. intros. simpl. rewrite H.
    destruct (Nat.eq_dec n0 m); destruct (Nat.eq_dec n0 n); reflexivity.
  Qed.
End SameProperties.

#[export] Hint Resolve
  same_reflexivity same_symmetry same_transitivity 
  same_cons same_permutation : sortHDB.

Definition SortSpec :=
  (* алгоритм сортування є                                                    *)
  { f  (* функцією, що перетворює список на список                            *)
    | (forall lst, same lst (f lst)) /\  (* зберігає склад списку             *)
      (forall lst, sorted (f lst)) }.    (* та утворює відсортований список   *)

Fixpoint aux_ins_sort (n : nat) (lst : list nat) : list nat :=
  match lst with
  | [] => [n]
  | m :: lst' => if le_gt_dec n m then n :: m :: lst'
                 else m :: (aux_ins_sort n lst')
  end.

Lemma aux_ins_sort_same : forall n lst, same (aux_ins_sort n lst) (n :: lst).
Proof.
  intros. revert n. 
  induction lst as [| m lst' IHlst'].
  - auto with sortHDB.
  - intros n k. simpl aux_ins_sort.
    destruct (le_gt_dec n m).
    + reflexivity.
    + assert (occnum k (n :: m :: lst') = occnum k (m :: n :: lst')). {
        rewrite same_permutation with lst' lst' _ _ _; auto with sortHDB. }
      rewrite H.
      now apply same_cons.
Qed.

Fixpoint ins_sort (lst : list nat) : list nat :=
  match lst with
  | [] => []
  | n :: lst' => aux_ins_sort n (ins_sort lst')
  end.
Eval simpl in ins_sort [5; 4; 3; 2; 1].

Lemma gt_le : forall n m, n > m -> m <= n.
Proof.
  unfold "_ > _". intros.
  assert (m <= S m). { repeat constructor. }
  apply Nat.le_trans with (m := S m); assumption.
Qed.

Lemma aux_ins_sort_inv :
  forall n lst, sorted lst -> sorted (aux_ins_sort n lst).
Proof.
  intros. elim H; simpl; auto with sortHDB.
  - intro m. destruct (le_gt_dec n m); constructor; 
    assumption || constructor || now apply gt_le.
  - intros m k lst' H1 H2 H3. 
    destruct (le_gt_dec n m); simpl.
    + repeat constructor; try assumption.
    + destruct (le_gt_dec n k); simpl; constructor; try assumption.
      now apply gt_le.
Qed.

Theorem ins_sort_certified : SortSpec.
Proof. 
  exists ins_sort.
  split; intro.
  - unfold same. intro.
    induction lst as [| m lst' IHlst'].
    + reflexivity.
    + simpl. destruct (Nat.eq_dec n m).
      * assert (same (aux_ins_sort m (ins_sort lst')) (m :: (ins_sort lst'))). 
        { apply aux_ins_sort_same. }
        rewrite H. rewrite <- e. simpl.
        destruct (Nat.eq_dec n n); try contradiction.
          rewrite IHlst'; reflexivity.
      * simpl. destruct (Nat.eq_dec n m); try contradiction.
          rewrite IHlst'.
          assert (
            same (aux_ins_sort m (ins_sort lst')) ( m :: ins_sort lst')).
          { apply aux_ins_sort_same. }
          rewrite H. simpl. destruct (Nat.eq_dec n m). try contradiction.
          reflexivity.
  - induction lst as [| n lst' IHlst'].
    + auto with sortHDB.
    + simpl. now apply aux_ins_sort_inv.
Qed.
