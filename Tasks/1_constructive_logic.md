Доведіть наступні факти, використовуючи The Coq Proof Assistant: 

```
Theorem ex1_1: forall A : Prop, A -> A. 

Theorem ex1_2: forall A B C : Prop, (A -> (B -> C)) -> ((A -> B) -> (A -> C)). 

Theorem ex1_3: forall A B C D: Prop, (A -> C)/\(B -> D) -> A/\B -> C/\D. 

Theorem ex1_4: forall A : Prop, A -> ∼ ∼ A.
```
