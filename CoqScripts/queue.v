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
; Queue6: forall  x y q, top (append x (append y q)) = top (append y q)
; Queue7: forall x, pop (append x empty) = Some empty
; Queue8: forall x y q q',
    Some q' = pop (append y q) ->
    pop (append x (append y q)) = Some (append x q')
; Queue9: forall P: queue -> Prop,
    P empty -> (forall x q, P q -> P (append x q)) -> forall q, P q
}.
