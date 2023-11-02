Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.


Module Type STACK.
  Parameter data stack : Set.
  Parameter null : stack.
  Parameter push : data -> stack -> stack.
  Parameter top : stack -> option data.
  Parameter pop : stack -> option stack.
  Parameter size : stack -> nat.

  Parameter data_eq_dec : forall x y : data, {x = y} + {x <> y}.

  Axiom null_top : forall s, top s = None <-> s = null.
  Axiom null_pop : forall s, pop s = None <-> s = null.

  Axiom push_top : forall s x, top (push x s) = Some x.
  Axiom push_pop : forall s x, pop (push x s) = Some s.
  Axiom push_size : forall s x, size (push x s) = S (size s).
  (*
  Axiom push_eq : 
    forall s' s'' x' x'', push x' s' = push x'' s'' -> x' = x'' /\ s' = s''.
  *)

  Axiom size_ind0 : forall s, size s = 0 <-> s = null.
  Axiom size_indS : 
    forall s n, size s = S n <-> exists s' x, size s' = n /\ s = push x s'.
End STACK.

Module Stack (S : STACK) <: STACK.
  Definition data := S.data.
  Definition stack := S.stack.
  Definition null := S.null.
  Definition top := S.top.
  Definition push := S.push.
  Definition pop := S.pop.
  Definition size := S.size.

  Definition data_eq_dec := S.data_eq_dec.

  Lemma null_top : forall s, top s = None <-> s = null.
  Proof. exact S.null_top. Qed.

  Lemma null_pop : forall s, pop s = None <-> s = null.
  Proof. exact S.null_pop. Qed.

  Lemma push_top : forall s x, top (push x s) = Some x.
  Proof. exact S.push_top. Qed.

  Lemma push_pop : forall s x, pop (push x s) = Some s.
  Proof. exact S.push_pop. Qed.

  Lemma push_size : forall s x, size (push x s) = S (size s).
  Proof. exact S.push_size. Qed.

  Lemma size_ind0 : forall s, size s = 0 <-> s = null.
  Proof. exact S.size_ind0. Qed.

  Lemma size_indS : 
    forall s n, size s = S n <-> exists s' x, size s' = n /\ s = push x s'.
  Proof. exact S.size_indS. Qed.

  (*
  Lemma push_eq : 
    forall s' s'' x' x'', push x' s' = push x'' s'' -> x' = x'' /\ s' = s''.
  Proof. exact S.push_eq. Qed.
  *)


  (* --------------------------Additional fields ---------------------------- *)

  Definition null_dec : forall s, {s = null} + {s <> null}.
  Proof.
    intro.
    destruct (top s) as [x |] eqn: E.
    - right. intro. rewrite H in E.
      assert (top null = None). { now apply null_top. }
      rewrite H0 in E. discriminate E.
    - left. now apply null_top.
  Defined.

  Lemma top_pop_push : 
    forall s x s', top s = Some x -> pop s = Some s' -> s = push x s'.
  Proof.
    intro.
    destruct (size s) eqn: E.
    - intros. assert (s = null). { now apply size_ind0. }
      rewrite H1 in H.
      assert (top null = None). { now apply null_top. }
      rewrite H2 in H. discriminate H.
    - pose (H := proj1 (size_indS s n) E).
      destruct H as (s', H).
      destruct H as (x, H). intros.
      pose (E1 := push_pop s' x). rewrite <- (proj2 H) in E1. rewrite E1 in H1.
      assert (H2 : s' = s'0). { now injection H1. }
      rewrite <- H2.
      pose (E2 := push_top s' x). rewrite <- (proj2 H) in E2. rewrite E2 in H0.
      assert (H3 : x = x0). { now injection H0. }
      now rewrite <- H3.
  Qed.

  Inductive reachable : stack -> Prop :=
    | reach0 : reachable null
    | reashS : forall s x, reachable s -> reachable (push x s).

  Theorem reachability : forall s, reachable s.
  Proof.
    intro. remember (size s).
    destruct (null_dec s) as [E | NE].
    - rewrite E. constructor.
    - revert s Heqn NE. induction n as [| n' IHn']; intros.
      + assert (s = null). { now apply size_ind0. }
        contradiction.
      + symmetry in Heqn.
        pose (H1 := proj1 (size_indS s n') Heqn).
        destruct H1 as (s', H1). destruct H1 as (x, H1).
        assert(reachable s'). {
          destruct (null_dec s') as [Nulls' | NotNulls'].
          - rewrite Nulls'. constructor.
          - apply IHn'.
            + symmetry. exact (proj1 H1).
            + assumption. }
        pose (H2 := proj2 H1). rewrite H2.
        now constructor.
  Qed.
End Stack.


