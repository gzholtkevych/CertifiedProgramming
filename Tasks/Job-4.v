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


Section ListStack.
(* Наведіть ТУТ таку реалізацію стеку:
   - stack:= list data
   - empty - порожній список
   - push - додавання елементу даних на початку списку
   - pop - видалення елементу з початку списку
   - top - повертає елемент з початку списку, без його видалення
   - isempty - повертає true, якщо список порожній, інакше повертає false
  *)
End ListStack.

