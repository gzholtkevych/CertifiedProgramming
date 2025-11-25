(*
Module Type TSTACK.
Parameter data: Set.
Parameter Stack: Set.
Parameter empty: Stack.
Parameter push: data -> Stack -> Stack.
Parameter pop: Stack -> option Stack.
Parameter top: Stack -> option data.

Parameter eq_dec: forall s' s'': Stack, {s' = s''} + {s' <> s''}.
End TSTACK.

Module InductiveStack: TSTACK.*)

Section InductiveSet.
Variable data: Set.
Variable data_eq_dec: forall x y: data, {x = y} + {x <> y}.

Inductive Stack: Set:=
  | empty: Stack
  | push: data -> Stack -> Stack.

Fixpoint size (s: Stack): nat:=
  match s with
    | empty => 0
    | push x s' => S (size s')
  end.

Lemma xx: forall x s, push x s <> s.
Proof.
  intros. intro.
  assert (size (push x s) = size s). { rewrite H. reflexivity. }
  simpl in H0.
 pose (n:= size s). intro. pose (m:= size (push x s)).
  simpl in m. subst n m.
  
  induction n as [| n' IHn'].
  induction s as [| y s' IHs'].
  - intros * H. discriminate H.
  - intros * H. apply (IHs' y). revert y H. inversion_clear H. 


Definition stack_eq_dec (s' s'': Stack): {s' = s''} + {s' <> s''}.
Proof.
  destruct s' as [| x' ss']; induction s'' as [| x'' ss'' IHss''].
  - now left.
  - right. intro.  discriminate H.
  - right. intro.  discriminate H.
  - destruct IHss'' as [IHss'' | IHss''].
    + right. intro. injection H. intros.


Definition pop {data: Set} (s: Stack data): option (Stack data):=
  match s with
    | empty     => None
    | push x s' => Some s'
  end.

Definition stack_eq_dec {data: Set} (s' s'': Stack data):
  {s' = s''} + {s' <> s''}.
Proof.
  induction s', s''.
  - now left.
  - right. intro. discriminate H.
  - right. intro. discriminate H.
  - destruct IHs'.
    + right. rewrite <- e. intro. induction s'. discriminate H.

Definition top {data: Set} (s: Stack data): option data:=
  match s with
    | empty => None
    | push x s' => Some x
  end.

Definition is_empty_dec {data: Set} (s: Stack data):
  {is_empty s = true} + {is_empty s = false}.
Proof. destruct (is_empty s); [left | right]; reflexivity. Defined.

Inductive Reachable {data: Set}: Stack data -> Prop:=
  | reah0: Reachable empty
  | reach_next: forall x s, Reachable s -> Reachable (push x s).

Lemma reachability {data: Set}: forall s: Stack data, Reachable s.
Proof.
  intro.
  induction s as [| x s' IHs']; constructor.
  assumption.
Qed.

Definition xx {data: Set}: forall s: Stack data,
  {is_empty s = true} + {Reachable s}.
Proof.
  intro.
  induction s as [| x s' IHs'].
  - left. reflexivity.
  - destruct IHs' as [H | H].
    + destruct s' as [| y s']. right. do 2 constructor.
      compute in H. discriminate H.
    + 
      constructor. constructor. compute in H. constructor.  reflexivity.
