Require Import SystemFR.Syntax.
Require Import SystemFR.Sets.
Require Import SystemFR.Tactics.
Require Import SystemFR.SetLemmas.
Require Import SystemFR.AssocList.
Require Import SystemFR.ListUtils.
Require Import SystemFR.EqualWithRelation.
Require Import SystemFR.EquivalentWithRelation.

Require Import PeanoNat.

Open Scope list_scope.

Fixpoint idrel (l: list nat) :=
  match l with
  | nil => nil
  | x :: xs => (x,x) :: idrel xs
  end.

Lemma idrel_lookup:
  forall l x,
    x ∈ l ->
    lookup Nat.eq_dec (idrel l) x = Some x.
Proof.
  induction l; steps.
Qed.

Lemma idrel_lookup_swap:
  forall l x,
    x ∈ l ->
    lookup Nat.eq_dec (swap (idrel l)) x = Some x.
Proof.
  induction l; steps.
Qed.

Lemma equal_with_idrel:
  forall t, equal_with_relation (idrel (pfv t type_var)) t t.
Proof.
  intros; apply equal_with_relation_refl2; steps;
    eauto using idrel_lookup, idrel_lookup_swap.
Qed.

Lemma idrel_lookup_fail:
  forall l x,
    (x ∈ l -> False) ->
    lookup Nat.eq_dec (idrel l) x = None.
Proof.
  induction l; steps.
Qed.

Lemma idrel_lookup_swap_fail:
  forall l x,
    (x ∈ l -> False) ->
    lookup Nat.eq_dec (swap (idrel l)) x = None.
Proof.
  induction l; steps.
Qed.

Lemma support_idrel:
  forall l, support (idrel l) = l.
Proof.
  induction l; steps.
Qed.

Lemma range_idrel:
  forall l, range (idrel l) = l.
Proof.
  induction l; steps.
Qed.

Lemma support_swap:
  forall l, support (swap l) = range l.
Proof.
  induction l; steps.
Qed.

Lemma range_swap:
  forall l, range (swap l) = support l.
Proof.
  induction l; steps.
Qed.

Lemma equivalent_rc_refl:
  forall rc, equivalent_rc rc rc.
Proof.
  unfold equivalent_rc; steps.
Qed.

Lemma equivalent_with_idrel:
  forall T (l: list nat) (x: nat) theta t (equiv: T -> T -> Prop),
    (x ∈ l -> False) ->
    (forall v, equiv v v) ->
    equivalent_with_relation (idrel l) theta ((x,t) :: theta) equiv.
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup ||
           rewrite support_idrel in * ||
           rewrite support_swap in * ||
           rewrite range_idrel in * ||
           rewrite range_swap in * ||
           (rewrite idrel_lookup in * by auto) ||
           (rewrite idrel_lookup_swap_fail in * by auto) ||
           apply equivalent_at_right.
Qed.

Lemma equivalent_with_idrel2:
  forall T (l: list nat) (x: nat) theta t (equiv: T -> T -> Prop),
    (x ∈ l -> False) ->
    (forall v, equiv v v) ->
    equivalent_with_relation (idrel l) ((x,t) :: theta) theta equiv.
Proof.
  unfold equivalent_with_relation;
    repeat step || t_lookup ||
           rewrite support_idrel in * ||
           rewrite support_swap in * ||
           rewrite range_idrel in * ||
           rewrite range_swap in * ||
           (rewrite idrel_lookup in * by auto) ||
           (rewrite idrel_lookup_swap_fail in * by auto) ||
           apply equivalent_at_left.
Qed.

Ltac t_idrel :=
  rewrite support_idrel in * ||
  rewrite support_swap in * ||
  rewrite range_idrel in * ||
  rewrite range_swap in * ||
  (rewrite idrel_lookup in * by auto) ||
  (rewrite idrel_lookup_swap_fail in * by auto).

Lemma equivalent_with_relation_permute:
  forall T theta1 theta2 v M l (equiv: T -> T -> Prop),
    ~(M ∈ support theta1) ->
    (forall v, equiv v v) ->
    equivalent_with_relation
      ((M, M) :: idrel l)
      (theta1 ++ (M, v) :: theta2)
      ((M, v) :: theta1 ++ theta2)
      equiv
.
Proof.
  unfold equivalent_with_relation, equivalent_at;
    repeat match goal with
           | |- exists r, Some ?R = Some r /\ _ => exists R
           | |- exists r, _ /\ equivalent_rc r ?R => exists R
           | H: _ |- _ => rewrite lookup_remove2 in H by steps
           | _ => rewrite lookup_remove2 by steps
           | _ => step || t_lookup_rewrite || t_idrel || t_lookup || t_listutils ||
                 rewrite obvious_lookup in * by steps ||
                 t_lookupor || t_lookup_same
           end;
    eauto.
Qed.

Lemma idrel_lookup2:
  forall x y l eq_dec, lookup eq_dec (idrel l) x = Some y -> x = y /\ x ∈ l.
Proof.
  induction l; repeat step || eapply_any || instantiate_any.
Qed.

Ltac t_idrel_lookup2 :=
  match goal with
  | H: lookup _ (idrel ?l) ?x = Some ?y |- _ => pose proof (idrel_lookup2 _ _ _ _ H); clear H
  end.

Lemma swap_idrel:
  forall l, swap (idrel l) = idrel l.
Proof.
  induction l; steps.
Qed.

Lemma equivalent_with_relation_permute2:
  forall T theta1 theta2 v X Y l (equiv: T -> T -> Prop),
    ~(X ∈ support theta1) ->
    (forall v, equiv v v) ->
    equivalent_with_relation
      ((Y, X) :: idrel l)
      ((Y, v) :: theta1 ++ theta2)
      (theta1 ++ (X, v) :: theta2)
      equiv
.
Proof.
  unfold equivalent_with_relation, equivalent_at;
    repeat match goal with
           | |- exists r, Some ?R = Some r /\ _ => exists R
           | |- exists r, _ /\ equivalent_rc r ?R => exists R
           | H: _ |- _ => rewrite lookup_remove2 in H by steps
           | _ => rewrite lookup_remove2 by steps
           | _ => step || t_lookup_rewrite || t_idrel || t_lookup || t_listutils ||
                 rewrite obvious_lookup in * by steps ||
                 t_lookupor || t_lookup_same
           end;
    eauto.
Qed.
