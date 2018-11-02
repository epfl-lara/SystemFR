Require Import Termination.AssocList.
Require Import Termination.Tactics.
Require Import Termination.Sets.
Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.ListUtils.

Require Import Termination.ReducibilityCandidate.

Require Import PeanoNat.

Open Scope list_scope.

Definition equivalent_rc (rc1 rc2: tree -> Prop) :=
  forall t, rc1 t <-> rc2 t.

Lemma equivalent_rc_left:
  forall rc1 rc2 t,
    equivalent_rc rc1 rc2 ->
    rc1 t ->
    rc2 t.
Proof.
  unfold equivalent_rc; intros; apply_any; assumption.
Qed.

Lemma equivalent_rc_right:
  forall rc1 rc2 t,
    equivalent_rc rc1 rc2 ->
    rc2 t ->
    rc1 t.
Proof.
  unfold equivalent_rc; intros; apply_any; assumption.
Qed.

Lemma equivalent_rc_sym:
  forall rc1 rc2, equivalent_rc rc1 rc2 -> equivalent_rc rc2 rc1.
Proof.
  unfold equivalent_rc; repeat step || apply_any.
Qed.

Definition equivalent_rc_at l1 l2 x y :=
  (forall rc1, lookup Nat.eq_dec l1 x = Some rc1 ->
  exists rc2, lookup Nat.eq_dec l2 y = Some rc2  /\ equivalent_rc rc1 rc2) /\
  (forall rc2, lookup Nat.eq_dec l2 y = Some rc2 ->
  exists rc1, lookup Nat.eq_dec l1 x = Some rc1  /\ equivalent_rc rc1 rc2).

Lemma equivalent_rc_at_sym:
  forall l1 l2 x y,
    equivalent_rc_at l1 l2 x y ->
    equivalent_rc_at l2 l1 y x.
Proof.
  unfold equivalent_rc_at; repeat step;
    try solve [ instantiate_any; steps; eauto using equivalent_rc_sym ].
Qed.

(*
Lemma equivalent_rc_at_add:
  forall l1 l2 x y,
    equivalent_rc rc1 rc2 ->
    equivalent_rc_at l1 l2 x y ->
    equivalent_rc_at l1 l2 y x.
Proof.
  unfold equivalent_rc_at; repeat step;
    try solve [ instantiate_any; steps; eauto using equivalent_rc_sym ].
Qed.
*)
Definition equivalent_with_relation rel l1 l2 :=
  forall x y,
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    equivalent_rc_at l1 l2 x y.

Lemma equivalent_with_relation_swap:
  forall l1 l2 rel,
    equivalent_with_relation rel l1 l2 ->
    equivalent_with_relation (swap rel) l2 l1.
Proof.
  unfold equivalent_with_relation;
    repeat step || rewrite swap_twice in *;
      eauto using equivalent_rc_at_sym.
Qed.

Lemma equivalent_rc_at_add:
  forall l1 l2 x y rc1 rc2,
    equivalent_rc rc1 rc2 ->
    equivalent_rc_at ((x,rc1) :: l1) ((y,rc2) :: l2) x y.
Proof.
  unfold equivalent_rc_at; steps; eauto.
Qed.

Lemma equivalent_rc_at_add2:
  forall l1 l2 x y x' y' rc1 rc2,
    x <> x' ->
    y <> y' ->
    equivalent_rc_at l1 l2 x y ->
    equivalent_rc_at ((x',rc1) :: l1) ((y',rc2) :: l2) x y.
Proof.
  unfold equivalent_rc_at; steps; eauto.
Qed.

Lemma equivalent_with_relation_add:
  forall l1 l2 x y rel rc1 rc2,
    equivalent_with_relation rel l1 l2 ->
    equivalent_rc rc1 rc2 ->
    equivalent_with_relation ((x,y) :: rel) ((x,rc1) :: l1) ((y,rc2) :: l2).
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup || apply equivalent_rc_at_add || apply equivalent_rc_at_add2.
Qed.

Lemma instantiate_rel:
  forall rel theta theta' x y P,
    equivalent_with_relation rel theta theta' ->
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    lookup Nat.eq_dec theta x = Some P ->
    (exists P', equivalent_rc P P' /\
           lookup Nat.eq_dec theta' y = Some P').
Proof.
  unfold equivalent_with_relation, equivalent_rc_at; intros;
  match goal with
  | H: forall x y, _, H1: _, H2: _ |- _ => pose proof (H _ _ H1 H2)
  end; steps.
  instantiate_any; repeat step || eauto || eexists.
Qed.

Lemma instantiate_rel2:
  forall rel theta theta' x y P',
    equivalent_with_relation rel theta theta' ->
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    lookup Nat.eq_dec theta' y = Some P' ->
    (exists P, equivalent_rc P P' /\
           lookup Nat.eq_dec theta x = Some P).
Proof.
  unfold equivalent_with_relation, equivalent_rc_at; intros;
  match goal with
  | H: forall x y, _, H1: _, H2: _ |- _ => pose proof (H _ _ H1 H2)
  end; steps.
  instantiate_any; repeat step || eauto || eexists.
Qed.

Ltac t_instantiate_rel :=
  lazymatch goal with
  | H1: equivalent_with_relation ?rel ?theta ?theta',
    H2: lookup _ ?rel ?x = Some ?y,
    H3: lookup _ (swap ?rel) ?y = Some ?x,
    H4: lookup _ ?theta ?x = Some ?t |- _ =>
      poseNew (Mark (x,y,t) "equivalent_with_relation");
      pose proof (instantiate_rel _ _ _ _ _ _ H1 H2 H3 H4)
  | H1: equivalent_with_relation ?rel ?theta ?theta',
    H2: lookup _ ?rel ?x = Some ?y,
    H3: lookup _ (swap ?rel) ?y = Some ?x,
    H4: lookup _ ?theta' ?y = Some ?t |- _ =>
      poseNew (Mark (x,y,t) "equivalent_with_relation");
      pose proof (instantiate_rel2 _ _ _ _ _ _ H1 H2 H3 H4)
  end.
