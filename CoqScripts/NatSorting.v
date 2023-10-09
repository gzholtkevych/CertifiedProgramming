Require Import Lists.List.
Import ListNotations.
Require Import Arith.PeanoNat.


Inductive sorted : list nat -> Prop :=
  | sort0 : (* порожній список є відсортованим                                *)
      sorted []
  | sort1 : (* будь-який одноелементний список є відсортованим                *)
      forall n, sorted [n]
  | sortS : (* якщо в голову відсортованого списку додати число меше
               за перший елемент списку, то отримаємо відсортований список    *)
      forall n m lst, 
        n <= m -> sorted (m :: lst) -> sorted (n :: m :: lst).

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
  (* визначення списків однакових за складом                                  *)
  fun lst' lst'' => forall n, occnum n lst' = occnum n lst''.

Definition SortSpec :=
  (* алгоритм сортування є                                                    *)
  { f : list nat -> list nat  (* функцією, що перетворює список на список     *)
    | (forall lst, same lst (f lst)) /\  (* зберігає склад списку             *)
      (forall lst, sorted (f lst)) }.    (* та утворює відсортований список   *)
