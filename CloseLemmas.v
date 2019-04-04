Require Import SystemFR.Tactics.
Require Import SystemFR.Sets.
Require Import SystemFR.Syntax.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.
Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.

Lemma close_nothing:
  forall x t k,
    ~(x ∈ pfv t term_var) ->
    close k t x = t.
Proof.
  induction t;
    repeat step || tequality || t_listutils.
Qed.

Lemma close_nothing2:
  forall x t k,
    pfv t term_var = nil ->
    close k t x = t.
Proof.
  intros; apply close_nothing; repeat step || rewrite_any.
Qed.

Lemma substitute_close:
  forall t l tag x k,
    ~(x ∈ support l) ->
    pclosed_mapping l term_var ->
    psubstitute (close k t x) l tag = close k (psubstitute t l tag) x.
Proof.
  induction t;
    repeat step || tequality || t_lookup || rewrite close_nothing2 by (steps; eauto with bfv).
Qed.

Lemma tclose_nothing:
  forall x t k,
    ~(x ∈ pfv t type_var) ->
    tclose k t x = t.
Proof.
  induction t;
    repeat step || tequality || t_listutils.
Qed.

Lemma tclose_nothing2:
  forall x t k,
    pfv t type_var = nil ->
    tclose k t x = t.
Proof.
  intros; apply tclose_nothing; repeat step || rewrite_any.
Qed.

Lemma substitute_tclose:
  forall t l tag x k,
    ~(x ∈ support l) ->
    pclosed_mapping l type_var ->
    psubstitute (tclose k t x) l tag = tclose k (psubstitute t l tag) x.
Proof.
  induction t;
    repeat step || tequality || t_lookup || rewrite tclose_nothing2 by (steps; eauto with bfv).
Qed.
