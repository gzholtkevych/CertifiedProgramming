Locate nat.
Print nat.  (* індуктивне визначення відповідає аксиомам
1. 0 є натуральним числом.
2. Длі будь-якого натурального числа n, S n є натуральним числом.

Аксиомам для рівності відповідають тактики
3. Для будь-якого n, вірно n = n (тактика reflexivity).
*)
Lemma eq_refl_nat : forall n : nat, n = n.
Proof. intro. reflexivity. Qed.
(*
4. Для будь-яких n та m, n = m гарантує m = n (тактика symmetry).
*)
Lemma eq_symm_nat : forall n m : nat, n = m -> m = n.
Proof. intros. symmetry. assumption. Qed.
(*
5. Для будь-яких n, m та k, n = m та m = k гарантують n = k (тактика
       transitivity).
*)
Lemma eq_trans_nat : forall n m k : nat, n = m -> m = k -> n = k.
Proof. intros * H1 H2. rewrite <- H2. assumption. Qed.
(*
Аксиомі ін'єктивності відповідає тактика injection.
6. Для будь-яких n та m, n = m тоді і тільки тоді, коли S n = S m. 
 *)
Lemma inj_nat : forall n m : nat, n = m <-> S n = S m.
Proof.
  intros. unfold "_ <-> _". split; intro.
  - rewrite H. reflexivity.
  - injection H. intro. assumption.
Qed.
Check inj_nat.
Print inj_nat.

(* Наступна аксиома гарантується тактикою discriminate
7. Для будь-якого n, не вірно S n = 0  *)
Lemma no_n_before_0 : forall n : nat, S n <> 0.
Proof. intros * H. discriminate H.
Qed.

(* Аксиома індукції генерується при визначені індуктивного типу
8. Для будь-якого предиката P, P 0 та P n -> P (S n) для всіх n гарантують,
   що P є тотожньо вірним. *)
Check nat_ind.

Print Nat.add.
Print Nat.mul.
Print Scope nat_scope.

(*
Натуральні числа з операцією додавання утворюють комутативний моноїд, тобто
додавання має нейтральний елемент, є асоціативним і комутативним.
*)
Lemma O_plus_n : forall n : nat, 0 + n = n.
Proof. (* intro. simpl. reflexivity. *) trivial. Qed.

Lemma n_plus_0 : forall n : nat, n + 0 = n.
Proof.
  intro.
  induction n as [| n' IHn'].
  - trivial.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma plus_assoc : forall n m k : nat, (n + m) + k = n + (m + k).
Proof.
  intros.
  induction n as [| n' IHn'].
  - trivial.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma n_plus_Sm: forall n m : nat, n + S m = S (n + m).
Proof.
  induction n as [| n' IHn']; intro.
  - trivial.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [| n' IHn']; intro.
  - rewrite n_plus_0. trivial.
  - simpl. rewrite IHn'. rewrite n_plus_Sm. reflexivity.
Qed.

(* Закон лівого скорочення                                                    *)
Lemma left_plus_cancel : forall n m k : nat, k + n = k + m -> n = m.
Proof.
  intros.
  induction k as [| k' IHk'].
  - (* simpl in H. assumption. *) trivial.
  - apply IHk'. clear IHk'.
    rewrite plus_comm in H. rewrite n_plus_Sm in H.
    replace (S k' + m) with (S (k' + m)) in H.
    + rewrite plus_comm. injection H. intro. assumption.
    + symmetry. 
      rewrite plus_comm. rewrite n_plus_Sm. rewrite plus_comm.
      reflexivity.
Qed.

(* Закон правого скорочення                                                   *)
Lemma right_plus_cancel : forall n m k : nat, n + k = m + k -> n = m.
Proof.
  intros.
  rewrite plus_comm in H.
  symmetry in H |-*. rewrite plus_comm in H.
  apply left_plus_cancel with k. assumption.
Qed.

Lemma O_mult_n (*15*) : forall n : nat, 0 * n = 0.
Admitted.

Lemma n_mult_0 (*15*) : forall n : nat, n * 0 = 0.
Admitted.

(* 1 = S 0 *)

Lemma unit_mult_n (*15*) : forall n : nat, 1 * n = n.
Admitted.

Lemma n_mult_unit (*15*) : forall n : nat, n * 1 = n.
Admitted.

Lemma mult_comm (*20*) : forall n m : nat, n * m = m * n.
Admitted.

Lemma mult_assoc (*20*) : forall n m k : nat, n * m * k = n * (m * k).
Admitted.

(* Відношення '<=' визначається як індуктивний предикат *)
Print le.
(* Це визначення еквівалентне такому
n <= m <-> exists k : nat, m = n + k *)
Lemma n_le_n_plus_m : forall n m : nat, n <= n + m.
Proof.
  intros *. revert n.
  induction m as [| m' IHm']; intro.
  - rewrite n_plus_0. constructor.
  - rewrite n_plus_Sm. constructor. exact (IHm' n).
Qed.

Lemma le_n_m : forall n m : nat, n <= m <-> exists k, m = n + k.
Proof.
  intros. split; intro.
  - induction H.
    + exists 0. trivial.
    + destruct IHle as (k, H1).
      exists (S k). rewrite n_plus_Sm. rewrite <- H1. reflexivity.
  - destruct H as (k, H1). rewrite H1. apply n_le_n_plus_m.
Qed.

Lemma le_refl : forall n : nat, n <= n.
Proof. intro. constructor. Qed.

Lemma le_trans : forall n m k : nat, n <= m -> m <= k -> n <= k.
Proof.
  intros.
  assert (H1 : exists k1, m = n + k1). { apply le_n_m. assumption. }
  assert (H2 : exists k2, k = m + k2). { apply le_n_m. assumption. }
  destruct H1 as (k1, H1). destruct H2 as (k2, H2).
  rewrite H1 in H2. rewrite plus_assoc in H2.
  apply le_n_m. exists (k1 + k2). assumption.
Qed.

Lemma le_asymm : forall n m : nat, n <= m -> m <= n -> n = m.
Admitted.
