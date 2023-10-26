(* -----------------------------------------------------------------------------
   This library contains definitions, properties, and certificates for
   the naming of entities.
   We assume that there is an enumerable set of names and a computable method 
   for distinguishing two different names.
   Therefore, natural numbers are used as names in the library.
   -------------------------------------------------------------------------- *)

Require Export Utf8.
Require Import Lists.List.
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.
Import ListNotations.


Module Type NAME.
  Parameter name : Set.
  Parameter id : name → nat.

  Axiom id_inj : ∀ x y : name, id x = id y → x = y.
  Axiom id_surj : ∀ n : nat, ∃ x : name, id x = n.
  Parameter eq_dec : ∀ x y : name, {x = y} + {x ≠ y}.
End NAME.

Module Names (M : NAME) <: NAME with Definition name := M.name.

  Definition name := M.name.
  Definition id := M.id.
  Definition id_inj := M.id_inj.
  Definition id_surj := M.id_surj.
  Definition eq_dec := M.eq_dec.


  Inductive increasing : list name → Prop :=
    | inc0 : increasing []
    | inc1 : ∀ n, increasing [n]
    | incS :
        ∀ n m lst,
          M.id n < M.id m → increasing (m :: lst) → increasing (n :: m :: lst).

  Definition inc_dec : ∀ lst : list name, {increasing lst} + {¬ increasing lst}.
  Proof.
    intro.
    destruct lst as [| n lst'].
    - left. constructor.
    - revert n. induction lst' as [| m lst'' IHlst'']; intro.
      + left. constructor.
      + destruct (lt_eq_lt_dec (M.id n) (M.id m)) as [Hle | HGt];
        try destruct Hle as [Hlt | Heq].
        * elim (IHlst'' m); intro H; [ left | right ];
          try now constructor.
          intro.
          assert (increasing (m :: lst'')). { now inversion_clear H0. }
          contradiction.
        * right. intro. inversion_clear H. rewrite Heq in H0.
          now apply Nat.lt_irrefl with (M.id m).
        * right. intro. inversion_clear H.
          apply Nat.lt_irrefl with (M.id n).
          now apply Nat.lt_trans with (M.id m).
  Defined.

  Definition NameSet := {lst : list name | increasing lst}.
  Coercion toList := fun ns : NameSet => proj1_sig ns.

  Definition In_dec : 
    ∀ (n : name) (ns : NameSet), {In n ns} + {¬ In n ns}.
  Proof.
    intros.
    destruct ns as (lst, H). simpl. clear H.
    induction lst as [| m lst' IHlst'].
    - right. intro. inversion_clear H.
    - destruct (M.eq_dec n m) as [Heq | Hneq];
      destruct (inc_dec lst') as [H1 | H1];
      try destruct(IHlst' H1) as [H2 | H2]; clear H1;
      try now (left; rewrite <- Heq; left).
      + destruct IHlst' as [H | H]; [ left | right ].
        * now right.
        * intro. apply H. elim H0; intro; 
          [ symmetry in H1; contradiction | assumption ].
      + destruct IHlst' as [H | H].
        * left. now right.
        * right. intro. simpl in H0. elim H0; intro;
         [ symmetry in H1; contradiction | contradiction ].
  Defined.

  Definition nothing : NameSet.
  Proof. exists []. constructor. Defined.

  Fixpoint aux_inject (n : name) (lst : list name) : list name :=
  (* the auxiliary function for injecting a name 'n' into a list of names 'lst'
     before the first member of the list that has 'id' greater than 'id n'.
   -------------------------------------------------------------------------- *)
    match lst with
    | []        => [n]
    | m :: lst' => match (lt_eq_lt_dec (M.id n) (M.id m)) with
        | inleft Hle => 
            match Hle with
            | left _  => n :: m :: lst'
            | right _ => m :: lst'
            end
        | inright _  => m :: (aux_inject n lst')
        end
    end.

  Definition inject (n : name) (ns : NameSet) : NameSet.
  (* the function Injects a name 'n' into a finite set of names 'ns' -------- *)
  Proof.
    destruct ns as (lst, H). pose (aux_inject n lst) as nlst.
    exists nlst. subst nlst.
    destruct lst as [| m lst'].
    - constructor.
    - simpl. destruct (lt_eq_lt_dec (M.id n) (M.id m)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now constructor.
      + assumption.
      + revert n m H Hgt. induction lst' as [| k lst'' IHlst''].
        * constructor; [assumption | constructor].
        * intros. {
          simpl. destruct (lt_eq_lt_dec (M.id n) (M.id k)) as [Hle | Hgt'];
          try destruct Hle as [Hlt | Heq].
          - constructor; [ assumption | constructor ]; try assumption.
            now inversion_clear H.
          - assumption.
          - inversion_clear H.
            constructor; try assumption. now apply IHlst''. }
  Defined.

  Lemma post_inject : ∀ n ns, In n (inject n ns).
  Proof.
    intros. revert n.
    destruct ns as (lst, H). simpl.
    induction lst as [| m lst' IHlst']; intro.
    - now constructor.
    - simpl. destruct (lt_eq_lt_dec (M.id n) (M.id m)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now constructor.
      + constructor. now apply M.id_inj.
      + right. apply IHlst'. inversion_clear H; [constructor | assumption].
  Qed.

  Lemma inject_discr : ∀ n m ns, In m (inject n ns) → n = m \/ In m ns.
  Proof.
    intros.
    destruct (eq_dec n m) as [Heq | HNeq].
    - now left.
    - destruct ns as (lst, Hinc). simpl in H |-*. right.
      induction lst.
      + simpl in H. destruct H as [H | H]; contradiction.
      + simpl in H. destruct (lt_eq_lt_dec (M.id n) (M.id a)) as [Hle | Hgt];
        try destruct Hle as [Hlt | Heq].
        * simpl in H |-*. now destruct H as [H | H].
        * destruct H as [H | H]; [now left | now right].
        * simpl in H. destruct H as [H | H];
          [now left | right]; apply IHlst;
          [ inversion_clear Hinc; [try now constructor | assumption]
          | assumption].
  Qed.

  Lemma inject_inv : ∀ n m (ns : NameSet), In n ns → In n (inject m ns).
  Proof.
    intros. destruct ns as (lst, Hinc).
    simpl in H |-*. revert n m H.
    induction lst as [| k lst' IHlst']; intros.
    - now left.
    - simpl. destruct (lt_eq_lt_dec (M.id m) (M.id k)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now right.
      + assumption.
      + elim H; intro.
        * now left.
        * right. apply IHlst'. 
          inversion_clear Hinc; [constructor | assumption]. assumption.
  Qed.

  Fixpoint declare (lst : list name) : NameSet :=
    match lst with
    | [] => nothing
    | n :: lst' => inject n (declare lst')
  end.

  Lemma post_declare : ∀ lst n, In n (declare lst) ↔ In n lst.
  Proof.
    intros. split; intro.
    - induction lst as [| m lst' IHlst'].
      + contradiction.
      + simpl in H.
        destruct (eq_dec m n) as [H1 | H1].
        * now left.
        * right. apply IHlst'.
          pose (H2 := inject_discr m n (declare lst') H).
          elim H2; intro; [contradiction | assumption].
    - revert n H. induction lst as [| m lst' IHlst']; intros.
      + contradiction.
      + elim H; intro H1.
        * rewrite H1. apply post_inject.
        * simpl. destruct (eq_dec n m) as [Heq | Hneq];
          [ rewrite Heq; apply post_inject
          | apply inject_inv; now apply IHlst' ].
  Qed.

End Names.

Inductive var := v : nat → var.
Module Var <: NAME with Definition name := var.
  Definition name := var.
  Definition id := fun x : name => let '(v n) := x in n.

  Lemma id_inj : ∀ x y : name, id x = id y → x = y.
  Proof. intros. destruct x as [n], y as [m]. simpl in H. now rewrite H. Qed.

  Lemma id_surj : ∀ n : nat, ∃ x : name, id x = n.
  Proof. intro. now exists (v n). Qed.

  Definition eq_dec : ∀ x y : name, {x = y} + {x ≠ y}.
  Proof.
    intros. destruct x as [n], y as [m].
    destruct (Nat.eq_dec n m) as [HEq | HNeq].
    - left. now rewrite HEq.
    - right. intro. apply HNeq. now injection H.
  Defined.
End Var.

Module varScopes := Names(Var).
