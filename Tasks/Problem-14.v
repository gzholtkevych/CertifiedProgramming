Require Classical.

(* Проведіть поданих нижче фактів доведення, розмістивши їх на місті
   "Admitted."                                                                *)

Theorem ex1: forall A B C : Prop, (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
Admitted.

Theorem ex2: forall A : Prop, A -> ~ ~ A.
Admitted.

Module Classic.
Import Classical.
(* Use classic : forall P : Prop, P \/ ~ P here                               *)

Theorem ex3: forall (a b : Type) (p : Type -> Prop),
  p a \/ p b -> exists x : Type, p x.
Admitted.

Theorem ex4: forall (A : Set) (R : A -> A -> Prop),
    (forall x y z : A, R x y /\ R y z -> R x z) ->
    (forall x y : A, R x y -> R y x) ->
    forall x : A, (exists y : A, R x y) -> R x x.
Admitted.

End Classic.

Theorem ex5 : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Admitted.
