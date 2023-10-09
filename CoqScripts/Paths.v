Require Import Lists.List.
Import ListNotations.


Inductive selector : Set := l | i | r.

Definition path : Set := list selector.

Lemma app_ind : forall P : path -> Prop,
  P [] ->
  (forall p s, P p -> P (p ++ [s])) ->
    forall p, P p.
Proof.
  intros * H0 HS *.
  destruct p as [| s p'].
  - assumption.
  - 

Inductive isPrefixOf : path -> path -> Prop :=
  | p_ipo_p  : forall p, isPrefixOf p p
  | p_ipo_ps : forall p pp s, isPrefixOf p pp -> isPrefixOf p (pp ++ [s]).

Notation "x 'ipo' y" := (isPrefixOf x y)  (at level 70).

Lemma pxChProp : forall p pp : path, p ipo pp <-> exists u : path, pp = p ++ u.
Proof.
  intros. split; intro.
  - induction H.
    + destruct p as [| s p'].
      * now exists [].
      * induction H. rewrite H0.