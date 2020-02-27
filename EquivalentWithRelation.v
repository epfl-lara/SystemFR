Require Import Coq.Strings.String.

Require Export SystemFR.AssocList.
Require Export SystemFR.Tactics.

Require Export SystemFR.ReducibilityCandidate.

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

Definition equivalent_with { T } (l1 l2: map nat T) (x y: nat) (equiv: T -> T -> Prop) :=
  (forall v1, lookup Nat.eq_dec l1 x = Some v1 ->
  exists v2, lookup Nat.eq_dec l2 y = Some v2  /\ equiv v1 v2) /\
  (forall v2, lookup Nat.eq_dec l2 y = Some v2 ->
  exists v1, lookup Nat.eq_dec l1 x = Some v1  /\ equiv v1 v2).

Lemma equivalent_with_refl:
  forall T theta x (equiv: T -> T -> Prop),
    (forall v, equiv v v) ->
    equivalent_with theta theta x x equiv.
Proof.
  unfold equivalent_with; steps; eauto.
Qed.

Lemma equivalent_with_sym:
  forall T (l1 l2: map nat T) x y (equiv: T -> T -> Prop),
    (forall x y, equiv x y -> equiv y x) ->
    equivalent_with l1 l2 x y equiv ->
    equivalent_with l2 l1 y x equiv.
Proof.
  unfold equivalent_with; repeat step;
    try solve [ instantiate_any; steps; eauto ].
Qed.

Definition equivalent_with_relation { T } rel (l1 l2: map nat T) equiv :=
  forall x y,
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    equivalent_with l1 l2 x y equiv.

Lemma equivalent_with_relation_swap:
  forall T (l1 l2: map nat T) rel (equiv: T -> T -> Prop),
    (forall x y, equiv x y -> equiv y x) ->
    equivalent_with_relation rel l1 l2 equiv ->
    equivalent_with_relation (swap rel) l2 l1 equiv.
Proof.
  unfold equivalent_with_relation;
    repeat step || rewrite swap_twice in *;
      eauto using equivalent_with_sym.
Qed.

Lemma equivalent_with_add:
  forall T l1 l2 x y v1 v2 (equiv: T -> T -> Prop),
    equiv v1 v2 ->
    equivalent_with ((x,v1) :: l1) ((y,v2) :: l2) x y equiv.
Proof.
  unfold equivalent_with; steps; eauto.
Qed.

Lemma equivalent_with_add2:
  forall T (l1 l2: map nat T) x y x' y' v1 v2 equiv,
    x <> x' ->
    y <> y' ->
    equivalent_with l1 l2 x y equiv ->
    equivalent_with ((x', v1) :: l1) ((y', v2) :: l2) x y equiv.
Proof.
  unfold equivalent_with; steps; eauto.
Qed.

Lemma equivalent_with_right:
  forall T x y theta t (equiv: T -> T -> Prop),
    x <> y ->
    (forall v, equiv v v) ->
    equivalent_with theta ((x,t) :: theta) y y equiv.
Proof.
  unfold equivalent_with; steps; eauto.
Qed.

Lemma equivalent_with_left:
  forall T x y theta t (equiv: T -> T -> Prop),
    x <> y ->
    (forall v, equiv v v) ->
    equivalent_with ((x,t) :: theta) theta y y equiv.
Proof.
  unfold equivalent_with; steps; eauto.
Qed.

Lemma equivalent_with_relation_add:
  forall T (l1 l2: map nat T) x y rel v1 v2 equiv,
    equivalent_with_relation rel l1 l2 equiv ->
    equiv v1 v2 ->
    equivalent_with_relation ((x,y) :: rel) ((x, v1) :: l1) ((y, v2) :: l2) equiv.
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup || apply equivalent_with_add || apply equivalent_with_add2.
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
  unfold equivalent_with_relation, equivalent_with; intros;
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
  unfold equivalent_with_relation, equivalent_with; intros;
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
