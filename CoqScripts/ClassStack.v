Require Import Arith.PeanoNat.


Module STACK.

Structure Data := declareData {
  data : Set;
  data_eqDec : forall x y : data, {x = y} + {x <> y}
}.


Section StackDefinition.
Variable value : Data.
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

Structure Stack := mkStack {
  value : Data;
  store : Set;
  null : store;
  push : data value -> store -> store;
  top : store -> option (data value);
  pop : store -> option store;
  size : store -> nat;
  gStack : aStack value store null push top pop size
}.

Section StackTheory.
Variable value : Data.
Variable stack : Stack.
Let store := store stack.
Let null := null stack.
Let push := push stack.
Let top := top stack.
Let pop := pop stack.
Let size := size stack.


  Definition null_dec : forall s, {s = null} + {s <> null}.
  Proof.
    destruct (gStack stack) as (null_top, _, _, _, _, _, _).
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
    destruct (gStack stack) as (
      null_top, _, push_top, push_pop, _, store_ind0, store_indS).
    intro.
    destruct (size s) eqn: E.
    - intros. assert (s = null). { now apply store_ind0. }
      rewrite H1 in H.
      assert (top null = None). { now apply null_top. }
      rewrite H2 in H. discriminate H.
    - pose (H := proj1 (store_indS n s) E).
      destruct H as (s', H).
      destruct H as (x, H). intros.
      pose (E1 := push_pop s' x). 
      rewrite <- (proj2 H) in E1. subst pop. rewrite E1 in H1.
      assert (H2 : s' = s'0). { now injection H1. }
      rewrite <- H2.
      pose (E2 := push_top s' x).
      rewrite <- (proj2 H) in E2. subst top. rewrite E2 in H0.
      assert (H3 : x = x0). { now injection H0. }
      now rewrite <- H3.
  Qed.


End StackTheory.

End STACK.


