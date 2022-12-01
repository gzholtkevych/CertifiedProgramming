Доведіть наступні факти, використовуючи The Coq Proof Assistant, попередньо виконавши команду

```
Require Import Classical.
```

для завантаження оточення, що містить принцип виключення третього:

```
Theorem ex2_1: forall a : Prop, ∼ ∼ a -> a. 

Theorem ex2_2: forall (p q : Type -> Prop) (a : Type), p a -> (forall x : Type, p x -> q x) -> q a. 

Theorem ex2_3: forall (a b : Type) (p : Type -> Prop), p a \/ p b -> exists x : Type, p x. 

Theorem ex2_4: forall (A : Set) (R : A -> A -> Prop),
    (forall x y z : A, R x y /\ R y z -> R x z) ->
    (forall x y : A, R x y -> R y x) ->
    forall x : A, (exists y : A, R x y) -> R x x.
