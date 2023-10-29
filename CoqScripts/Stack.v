Module Type STACK.
  Parameter data stack : Set.
  Parameter null : stack.
  Parameter push : data -> stack -> stack.
  Parameter top : stack -> option data.
  Parameter pop : stack -> option stack.

  Parameter data_eq_dec : forall x y : data, {x = y} + {x <> y}.
  Axiom null_top : forall s, top s = None <-> s = null.
  Axiom null_pop : forall s, pop s = None <-> s = null.
  Axiom push_top : forall s x, top (push x s) = Some x.
  Axiom push_pop : forall s x, pop (push x s) = Some s.
  Axiom top_pop_push : 
    forall s x s', top s = Some x -> pop s = Some s' -> s = push x s'.
End STACK.

Module Stack (S : STACK) <: STACK.
  Definition data := S.data.
  Definition stack := S.stack.
  Definition null := S.null.
  Definition top := S.top.
  Definition push := S.push.
  Definition pop := S.pop.

  Definition data_eq_dec := S.data_eq_dec.

  Lemma null_top : forall s, top s = None <-> s = null.
  Proof. exact S.null_top. Qed.

  Lemma null_pop : forall s, pop s = None <-> s = null.
  Proof. exact S.null_pop. Qed.

  Lemma push_top : forall s x, top (push x s) = Some x.
  Proof. exact S.push_top. Qed.

  Lemma push_pop : forall s x, pop (push x s) = Some s.
  Proof. exact S.push_pop. Qed.

  Lemma top_pop_push : 
    forall s x s', top s = Some x -> pop s = Some s' -> s = push x s'.
  Proof. exact S.top_pop_push. Qed.

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

  Lemma top_some : forall s, s <> null -> exists x, top s = Some x.
  Proof.
    intros. destruct (top s) as [x |] eqn: E.
    - now exists x.
    - assert (s = null). { now apply null_top. }
      contradiction.
  Qed.

  Lemma pop_some : forall s, s <> null -> exists s', pop s = Some s'.
  Proof.
    intros. destruct (pop s) as [s' |] eqn: E.
    - now exists s'.
    - assert (s = null). { now apply null_pop. }
      contradiction.
  Qed.
End Stack.


