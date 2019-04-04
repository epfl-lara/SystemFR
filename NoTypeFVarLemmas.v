Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.
Require Import SystemFR.AssocList.
Require Import SystemFR.NoTypeFVar.
Require Import SystemFR.EqualWithRelation.

Require Import PeanoNat.

Definition similar_sets (rel: map nat nat) (vars vars': list nat): Prop :=
  forall x y,
    lookup Nat.eq_dec rel x = Some y ->
    lookup Nat.eq_dec (swap rel) y = Some x ->
    (x ∈ vars <-> y ∈ vars').

Lemma no_type_fvar_rename:
  forall T T' vars vars' rel,
    no_type_fvar T vars ->
    equal_with_relation rel T T' ->
    similar_sets rel vars vars' ->
    no_type_fvar T' vars'.
Proof.
  unfold no_type_fvar, similar_sets;
    repeat step || t_equal_with_relation_pfv2 || t_lookup_same;
    eauto with beapply_any.
Qed.
