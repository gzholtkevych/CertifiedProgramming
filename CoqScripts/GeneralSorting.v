

Check comparison.
Print comparison.

Module Type Comparable.
  Parameter X : Set.
  Parameter cmp : X -> X -> comparison.
  
  Axiom cmp1 : forall x y, cmp x y = Eq <-> x = y.
  Axiom cmp2 : forall x y, cmp x y = Lt <-> cmp y x = Gt.
  Axiom cmp3 : forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.
End Comparable.

Module Type Ordered.
  Parameter X : Set.
  Parameter lt : X -> X -> Prop.
  Parameter lt_eq_lt_dec : forall x y, {lt x y} + {x = y} + {lt y x}.
  
  Axiom lt_irrefl : forall x, ~ lt x x.
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
End Ordered.

Module Comparable_to_Ordered (C : Comparable) : Ordered.
  Definition X := C.X.
  Definition lt := fun x y => C.cmp x y = Lt.
  Definition lt_eq_lt_dec (x y : X) : {lt x y} + {x = y} + {lt y x}.
  Proof.
    destruct (C.cmp x y) eqn : V.
    - left. right. apply C.cmp1. assumption.
    - left. left. assumption.
    - right. apply C.cmp2. assumption.
  Defined.
  
  Lemma lt_irrefl : forall x, ~ lt x x.
  Proof.
    intros * H. unfold lt in H.
    assert (C.cmp x x = Eq). { apply C.cmp1. reflexivity. }
    rewrite H0 in H. discriminate H.
  Qed.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. exact C.cmp3.
  Qed.
End Comparable_to_Ordered.


