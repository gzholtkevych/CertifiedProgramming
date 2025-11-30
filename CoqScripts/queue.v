Require Import Lists.List.
Import ListNotations.


Class aQueue (data: Set) (queue: Set)
  (empty: queue)
  (append: data -> queue -> queue)
  (pop: queue -> option queue)
  (top: queue -> option data)
  (isempty: queue -> bool): Prop:=
{ Queue1: isempty empty = true
; Queue2: forall x q, isempty (append x q) = false
; Queue3: pop empty = None
; Queue4: top empty = None
; Queue5: forall x, top (append x empty) = Some x
; Queue6: forall x y q, top (append x (append y q)) = top (append y q)
; Queue7: forall x, pop (append x empty) = Some empty
; Queue8: forall x y q q',
    Some q' = pop (append y q) ->
    pop (append x (append y q)) = Some (append x q')
; Queue9: forall P: queue -> Prop,
    P empty -> (forall x q, P q -> P (append x q)) -> forall q, P q
}.


Section InductiveQueue.
Variable data: Set.

Inductive IQueue: Set:=
  | iqempty: IQueue
  | iqappend: forall (x: data), IQueue -> IQueue.

Fixpoint iqpop (q: IQueue): option IQueue:=
  match q with
    | iqempty => None
    | iqappend x q' => match iqpop q' with
        | Some u => Some (iqappend x u)
        | None   => Some iqempty
      end
  end.

Fixpoint iqtop (q: IQueue): option data:=
  match q with
    | iqempty       => None
    | iqappend x q' => match iqtop q' with
        | Some u => Some u
        | _      => Some x
      end
  end.

Definition iqisempty (q: IQueue): bool:=
  match q with
    | iqempty => true
    | _       => false
  end.


Instance IQueueRealization:
  aQueue data IQueue iqempty iqappend iqpop iqtop iqisempty.
Proof.
  constructor; trivial.
  - intros *. simpl. destruct (iqtop q); reflexivity.
  - intros *. simpl. intro. destruct (iqpop q).
    + assert (q' = iqappend y i). { injection H. trivial. }
      rewrite H0. reflexivity.
    + assert (q' = iqempty). { injection H. trivial. }
      rewrite H0. reflexivity.
  - intros * H0 H1 *.
    induction q as [| x q' IHq']; trivial.
    apply H1. assumption.
Defined. 
Section EndQueue.

Section ListQueue.
(* Наведіть ТУТ таку реалізацію черги:
   - queue:= list data
   - empty - порожній список
   - append - додавання елементу даних в кінці списку
   - pop - видалення елементу з початку списку
   - top - повертає елемент з початку списку, без його видалення
   - isempty - повертає true, якщо список порожній, інакше повертає false
  *)
End ListQueue.



