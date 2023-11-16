Lemma left_canc : forall n m : nat, n + m = m -> n = 0.
Proof.
  intros. revert n H.
  induction m as [| m' IHm']; intros.
  - rewrite <- H.
    apply plus_n_O.
  - apply IHm'. 
    rewrite <- plus_n_Sm in H.
    now injection H.
Qed.

Lemma left_canc_exellent : forall n m : nat, n + m = m -> n = 0.
Proof.
  intros. revert n H.
  (* індукцією за m доводимо *)
  induction m as [| m' IHm']; intros.
  - (* база індукції :*)
    (* заміна правої частини H лівою у цілі *) rewrite <- H.
    (* зводить доведення до стандартної леми *) apply plus_n_O.
  - (* індукційний перехід *) 
    (* застосовуємо припущення індукції *) apply IHm'. 
    (* використання стандартної рівності дає *) rewrite <- plus_n_Sm in H.
    (* застосування принципу ін'єктивності завершує доведення *) 
    now injection H.
Qed.