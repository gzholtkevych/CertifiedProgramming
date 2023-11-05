Require Import Arith.PeanoNat.


Module STACK.

Structure Data := declareData {
  data : Set;
  data_eqDec : forall x y : data, {x = y} + {x <> y}
}.


Section StackDefinition.
Context `{value : Data}.
Variables
  (store : Set)
  (null : store)
  (push : data value -> store -> store)
  (top : store -> option (data value))
  (pop : store -> option store)
  (size : store -> nat).


  Class aStack := {
    null_top : forall s, top s = None <-> s = null;
    null_pop : forall s, pop s = None <-> s = null;
    push_top : forall s x, top (push x s) = Some x;
    push_pop : forall s x, pop (push x s) = Some s;
    push_size : forall s x, size (push x s) = S (size s);
    store_ind0 : forall s, size s = 0 <-> s = null;
    store_indS : 
      forall n s, size s = S n <-> exists s' x, size s' = n /\ s = push x s'
  }.

End StackDefinition.


Section StackTheory.
Context `{value : Data}.
Variables
  (store : Set)
  (null : store)
  (push : data value -> store -> store)
  (top : store -> option (data value))
  (pop : store -> option store)
  (size : store -> nat).
Context `{G : aStack value store null push top pop size}.


  Definition null_dec : forall s, {s = null} + {s <> null}.
  Proof.
    destruct G as (null_top_G, _, _, _, _, _, _).
    intro.
    destruct (top s) as [x |] eqn: E.
    - right. intro. rewrite H in E.
      assert (top null = None). { now apply null_top_G. }
      rewrite H0 in E. discriminate E.
    - left. now apply null_top_G.
  Defined.


  Lemma top_pop_push : 
    forall s x s', top s = Some x -> pop s = Some s' -> s = push x s'.
  Proof.
    destruct G as (
      null_top_G, _, push_top_G, push_pop_G, _, store_ind0_G, store_indS_G).
    intro.
    destruct (size s) eqn: E.
    - intros. assert (s = null). { now apply store_ind0_G. }
      rewrite H1 in H.
      assert (top null = None). { now apply null_top_G. }
      rewrite H2 in H. discriminate H.
    - pose (H := proj1 (store_indS_G n s) E).
      destruct H as (s', H).
      destruct H as (x, H). intros.
      pose (E1 := push_pop_G s' x). 
      rewrite <- (proj2 H) in E1. rewrite E1 in H1.
      assert (H2 : s' = s'0). { now injection H1. }
      rewrite <- H2.
      pose (E2 := push_top_G s' x).
      rewrite <- (proj2 H) in E2. rewrite E2 in H0.
      assert (H3 : x = x0). { now injection H0. }
      now rewrite <- H3.
  Qed.


End StackTheory.

End STACK.


