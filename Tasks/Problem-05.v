Require Classical.

(* Проведіть поданих нижче фактів доведення, розмістивши їх на місті
   "Admitted."                                                                *)

Theorem ex1: forall A : Prop, A -> A.
Admitted.

Theorem ex2: forall A B C : Prop, (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
Admitted.

Module Classic.
Import Classical.
(* Use classic : forall P : Prop, P \/ ~ P here                               *)

Theorem ex3: forall (p q : Type -> Prop) (a : Type),
  p a -> (forall x : Type, p x -> q x) -> q a.
Admitted.

Theorem ex4: forall (a b : Type) (p : Type -> Prop),
  p a \/ p b -> exists x : Type, p x.
Admitted.

End Classic.

Theorem ex5: forall n : nat, S n <> 0.
Admitted.
