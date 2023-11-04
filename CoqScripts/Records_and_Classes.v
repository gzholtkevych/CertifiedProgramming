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

Definition origin := {| xc := 0; yc := 0 |}.
Eval compute in xc origin.
Eval compute in yc origin.

Class aMonoid (X : Set) (comp : X -> X-> X) (e : X) := {
  assoc : forall x y z, comp (comp x y) z = comp x (comp y z);
  left_unit : forall x, comp e x = x;
  right_unit : forall x, comp x e = x
}.

Section MonoidTheory.
Variables (X : Set) (comp : X -> X-> X) (e : X).
Context `{G : aMonoid X comp e}.

  Lemma unit_unieq : 
    forall u : X,
      (forall x : X, comp u x = x) ->
      (forall x : X, comp x u = x) ->
        u = e.
  Proof.
    intros.
    pose (Hue := H e). pose (Heu := H0 e).
    destruct G.
    pose(H1ue := right_unit0 u).
    now rewrite H1ue in Hue.
  Qed.
End MonoidTheory.