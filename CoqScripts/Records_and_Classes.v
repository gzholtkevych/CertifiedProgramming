Require Import Arith.PeanoNat.

(*
Inductive Pnt : Set :=
  pnt : nat -> nat -> Pnt.

Definition origin := pnt 0 0.

Definition xc (p : Pnt) : nat := let 'pnt x _ := p in x.
Definition yc (p : Pnt) : nat := let 'pnt _ y := p in y.

Eval compute in xc origin.
Eval compute in yc origin.
*)

Record Point : Set := pnt {
  xc : nat;
  yc : nat
}.
Check Point.
Print Point.
Check xc.
Print xc.

(*
Structure Point : Set := pnt {
  xc : nat;
  yc : nat
}.
*)

Definition origin : Point := {| xc := 0; yc := 0 |}.
Eval compute in xc origin.
Eval compute in yc origin.

Class aMonoid (X : Set) (comp : X -> X -> X) (e : X) := {
  assoc : forall x y z, comp (comp x y) z = comp x (comp y z);
  left_unit : forall x, comp e x = x;
  right_unit : forall x, comp x e = x
}.

Print aMonoid.

Structure Monoid := mkMonoid {
  X : Set;
  comp : X -> X -> X;
  e : X;
  gMonoid : aMonoid X comp e
}.

Instance nat_plus_monoid_instance : aMonoid nat plus 0.
Proof.
  constructor.
  - symmetry. apply Nat.add_assoc.
  - trivial.
  - symmetry. apply plus_n_O.
Defined.

Definition nat_plus_monoid := {|
  X := nat; comp := plus; e := 0; gMonoid := nat_plus_monoid_instance |}.


Section MonoidTheory.
Variable m : Monoid.
Let X := X m.
Let comp := comp m.
Let e := e m.

  Lemma unit_unieq : 
    forall u : X,
      (forall x : X, comp u x = x) ->
      (forall x : X, comp x u = x) ->
        u = e.
  Proof.
    intros * Hleft Hright.
    pose (Hleft_e := Hleft e). pose (Hright_e := Hright e).
    destruct (gMonoid m) as [assoc lunit runit].
    rewrite runit in Hleft_e. assumption.
  Qed.
End MonoidTheory.
Check unit_unieq.

Example O_unique := unit_unieq nat_plus_monoid.
