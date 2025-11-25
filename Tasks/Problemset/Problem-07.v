Require Classical.

(* Проведіть поданих нижче фактів доведення, розмістивши їх на місті
   "Admitted."                                                                *)

Theorem ex1: forall A : Prop, A -> A.
Admitted.

Theorem ex2: forall A B C D: Prop, (A -> C)/\(B -> D) -> A/\B -> C/\D.
Admitted.

Module Classic.
Import Classical.
(* Use classic : forall P : Prop, P \/ ~ P here                               *)

Theorem ex3: forall a : Prop, ~ ~ a -> a. 
Admitted.

Theorem ex4: forall (p q : Type -> Prop) (a : Type),
  p a -> (forall x : Type, p x -> q x) -> q a.
Admitted.

End Classic.

Theorem ex5 : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Admitted.
