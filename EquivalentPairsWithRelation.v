Require Import Coq.Strings.String.

Require Import SystemFR.AssocList.
Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.
Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.ListUtils.

Require Import PeanoNat.

Open Scope list_scope.

Fixpoint equivalent_pairs_with_relation { T } rel (l1 l2: map nat T) equiv :=
  match l1, l2 with
  | nil, nil => True
  | (x,a) :: l1', (y,b) :: l2' =>
    lookup Nat.eq_dec rel x = Some y /\
    lookup Nat.eq_dec (swap rel) y = Some x /\
    equiv a b /\
    equivalent_pairs_with_relation rel l1' l2' equiv
  | _, _ => False
  end.

(*
Lemma equivalent_with_relation_swap:
  forall T (l1 l2: map nat T) rel (equiv: T -> T -> Prop),
    (forall x y, equiv x y -> equiv y x) ->
    equivalent_with_relation rel l1 l2 equiv ->
    equivalent_with_relation (swap rel) l2 l1 equiv.
Proof.
  unfold equivalent_with_relation;
    repeat step || rewrite swap_twice in *;
      eauto using equivalent_at_sym.
Qed.

Lemma equivalent_at_add:
  forall T l1 l2 x y v1 v2 (equiv: T -> T -> Prop),
    equiv v1 v2 ->
    equivalent_at ((x,v1) :: l1) ((y,v2) :: l2) x y equiv.
Proof.
  unfold equivalent_at; steps; eauto.
Qed.

Lemma equivalent_at_add2:
  forall T (l1 l2: map nat T) x y x' y' v1 v2 equiv,
    x <> x' ->
    y <> y' ->
    equivalent_at l1 l2 x y equiv ->
    equivalent_at ((x', v1) :: l1) ((y', v2) :: l2) x y equiv.
Proof.
  unfold equivalent_at; steps; eauto.
Qed.

Lemma equivalent_at_right:
  forall T x y theta t (equiv: T -> T -> Prop),
    x <> y ->
    (forall v, equiv v v) ->
    equivalent_at theta ((x,t) :: theta) y y equiv.
Proof.
  unfold equivalent_at; steps; eauto.
Qed.

Lemma equivalent_at_left:
  forall T x y theta t (equiv: T -> T -> Prop),
    x <> y ->
    (forall v, equiv v v) ->
    equivalent_at ((x,t) :: theta) theta y y equiv.
Proof.
  unfold equivalent_at; steps; eauto.
Qed.

Lemma equivalent_with_relation_add:
  forall T (l1 l2: map nat T) x y rel v1 v2 equiv,
    equivalent_with_relation rel l1 l2 equiv ->
    equiv v1 v2 ->
    equivalent_with_relation ((x,y) :: rel) ((x, v1) :: l1) ((y, v2) :: l2) equiv.
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup || apply equivalent_at_add || apply equivalent_at_add2.
Qed.

Lemma instantiate_rel:
  forall T rel theta theta' x y P (equiv: T -> T -> Prop),
    equivalent_with_relation rel theta theta' equiv ->
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    lookup Nat.eq_dec theta x = Some P ->
    (exists P', equiv P P' /\
           lookup Nat.eq_dec theta' y = Some P').
Proof.
  unfold equivalent_with_relation, equivalent_at; intros;
  match goal with
  | H: forall x y, _, H1: _, H2: _ |- _ => pose proof (H _ _ H1 H2)
  end; steps.
  instantiate_any; repeat step || eauto || eexists.
Qed.

Lemma instantiate_rel2:
  forall T rel theta theta' x y P' (equiv: T -> T -> Prop),
    equivalent_with_relation rel theta theta' equiv ->
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    lookup Nat.eq_dec theta' y = Some P' ->
    (exists P, equiv P P' /\
           lookup Nat.eq_dec theta x = Some P).
Proof.
  unfold equivalent_with_relation, equivalent_at; intros;
  match goal with
  | H: forall x y, _, H1: _, H2: _ |- _ => pose proof (H _ _ H1 H2)
  end; steps.
  instantiate_any; repeat step || eauto || eexists.
Qed.

Ltac t_instantiate_rel :=
  lazymatch goal with
  | H1: equivalent_with_relation ?rel ?theta ?theta' ?equiv,
    H2: lookup _ ?rel ?x = Some ?y,
    H3: lookup _ (swap ?rel) ?y = Some ?x,
    H4: lookup _ ?theta ?x = Some ?t |- _ =>
      poseNew (Mark (x,y,t) "equivalent_with_relation");
      pose proof (instantiate_rel _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | H1: equivalent_with_relation ?rel ?theta ?theta' ?equiv,
    H2: lookup _ ?rel ?x = Some ?y,
    H3: lookup _ (swap ?rel) ?y = Some ?x,
    H4: lookup _ ?theta' ?y = Some ?t |- _ =>
      poseNew (Mark (x,y,t) "equivalent_with_relation");
      pose proof (instantiate_rel2 _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  end.
*)