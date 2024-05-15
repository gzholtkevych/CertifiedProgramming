Require Classical.

(* Проведіть поданих нижче фактів доведення, розмістивши їх на місті
   "Admitted."                                                                *)

Theorem 1: forall A : Prop, A -> A.
Admitted.

Theorem 2: forall A B C : Prop, (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
Admitted.

Module Classic.
Import Classical.
(* Use classic : forall P : Prop, P \/ ~ P here                               *)

Theorem 3: forall a : Prop, ~ ~ a -> a. 
Admitted.

Theorem ex4: forall (A : Set) (R : A -> A -> Prop),
    (forall x y z : A, R x y /\ R y z -> R x z) ->
    (forall x y : A, R x y -> R y x) ->
    forall x : A, (exists y : A, R x y) -> R x x.
Admitted.

End Classic.

Theorem ex5 : forall n m : nat, n + m = 1 -> n = 0 /\ m = 1 \/ n = 1 /\ m = 0.
Admitted.
