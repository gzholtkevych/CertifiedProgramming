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

Definition origin : Point := {| xc := 0; yc := 0 |}.
Eval compute in xc origin.
Eval compute in yc origin.

Class aMonoid (X : Set) (comp : X -> X-> X) (e : X) := {
  assoc : forall x y z, comp (comp x y) z = comp x (comp y z);
  left_unit : forall x, comp e x = x;
  right_unit : forall x, comp x e = x
}.

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
(*
  Let X := X m.
  Let comp := comp m.
  Let e := e m.
*)
  Lemma unit_unieq : 
    forall u : X m,
      (forall x : X m, (comp m) u x = x) ->
      (forall x : X m, (comp m) x u = x) ->
        u = e m.
  Proof.
    intros.
    pose (Hue := H (e m)). pose (Heu := H0 (e m)).
    destruct (gMonoid m).
    pose(H1ue := right_unit0).
    now rewrite H1ue in Hue.
  Qed.
End MonoidTheory.
Check unit_unieq.

Example O_unique := unit_unieq nat_plus_monoid.
Check O_unique.
