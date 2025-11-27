Require Import Lists.List.
Import ListNotations.


Class aStack
  (data: Set) (stack: Set)
  (empty: stack)
  (push: data -> stack -> stack)
  (pop: stack -> option stack)
  (top: stack -> option data)
  (isempty: stack -> bool): Prop:=
{ Stack1: isempty empty = true
; Stack2: forall x s, isempty (push x s) = false
; Stack3: pop empty = None
; Stack4: top empty = None
; Stack5: forall x s, pop (push x s) = Some s
; Stack6: forall x s, top (push x s) = Some x
; Stack7: forall (P: stack -> Prop),
    P empty -> (forall x s, P s -> P (push x s)) -> forall s, P s
}.

Section InductiveStack.
Variable data: Set.

Inductive IStack: Set:=
  | iempty: IStack
  | ipush: forall x: data, IStack -> IStack.

Definition ipop (s: IStack): option IStack:=
  match s with
    | iempty     => None
    | ipush x s' => Some s'
  end.

Definition itop (s: IStack) : option data:=
  match s with
    | iempty     => None
    | ipush x s' => Some x
  end.

Definition iisempty (s: IStack): bool:=
  match s with
    | iempty => true
    | _      => false
  end.


Instance IStackRealization:
  aStack data IStack iempty ipush ipop itop iisempty.
Proof.
  constructor.
  - simpl. reflexivity.
  - intros. simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
  - intros * H0 H1 s0.
    induction s0 as [| x s0' IHs0']; trivial.
    apply H1. assumption.
Defined.

End InductiveStack.


Section ListStack.
Variable data: Set.

Definition LStack:= list data.

Definition lempty:= @nil data.

Definition lpush (x: data) (s: LStack): LStack:= x :: s.

Definition lpop (s: LStack): option LStack:=
  match s with
    | []      => None
    | _ :: s' => Some s'
  end.

Definition ltop (s: LStack): option data:=
  match s with
    | []     => None
    | x :: _ => Some x
  end.

Definition lisempty (s: LStack): bool:=
  match s with
    | [] => true
    | _  => false
  end.

Instance LStackRealization:
  aStack data LStack lempty lpush lpop ltop lisempty.
Proof.
Admitted.

End ListStack.

