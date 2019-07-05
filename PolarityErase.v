Require Import Equations.Equations.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Syntax.
Require Import SystemFR.Trees.
Require Import SystemFR.Tactics.
Require Import SystemFR.Equivalence.
Require Import SystemFR.OpenTOpen.

Require Import SystemFR.SizeLemmas.

Require Import SystemFR.WFLemmas.
Require Import SystemFR.TWFLemmas.
Require Import SystemFR.ErasedTermLemmas.

Require Import SystemFR.IdRelation.
Require Import SystemFR.EqualWithRelation.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.

Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.AssocList.
Require Import SystemFR.Sets.
Require Import SystemFR.Freshness.
Require Import SystemFR.SwapHoles.
Require Import SystemFR.ListUtils.
Require Import SystemFR.TOpenTClose.
Require Import SystemFR.NoTypeFVar.

Require Import SystemFR.Polarity.
Require Import SystemFR.PolarityLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.NoTypeFVarLemmas.

Require Import SystemFR.TypeErasure.
Require Import SystemFR.TypeErasureLemmas.

Require Import SystemFR.AnnotatedTermLemmas.

Require Import SystemFR.TermList.

Opaque makeFresh.
Opaque Nat.eq_dec.

Lemma erase_type_topen2:
  forall T1 T2 k,
    is_annotated_type T1 ->
    erase_type T2 = T2 ->
    erase_type (topen k T1 T2) = topen k (erase_type T1) T2.
Proof.
  induction T1;
    repeat step || rewrite erase_term_topen in * || t_equality || rewrite topen_erase_term in *.
Qed.

Lemma has_polarities_erase_aux:
  forall n T pols,
    typeNodes T < n ->
    is_annotated_type T ->
    has_polarities T pols ->
    has_polarities (erase_type T) pols.
Proof.
  induction n; destruct T; steps; try omega;
    repeat
      step || step_inversion has_polarities || constructor || exists X || t_fv_erase ||
      rewrite <- erase_type_topen2 || apply_any || autorewrite with bsize in *;
        eauto with omega;
        eauto 2 with bannot step_tactic.
Qed.

Lemma has_polarities_erase:
  forall T pols,
    is_annotated_type T ->
    has_polarities T pols ->
    has_polarities (erase_type T) pols.
Proof.
  eauto using has_polarities_erase_aux.
Qed.

Lemma has_polarities_subst_aux:
  forall n T pols l,
    typeNodes T < n ->
    has_polarities T pols ->
    pclosed_mapping l type_var ->
    twfs l 0 ->
    has_polarities (psubstitute T l term_var) pols.
Proof.
  induction n; destruct T;
    repeat step || constructor || step_inversion has_polarities || exists X || t_pfv_in_subst || eapply_any ||
           autorewrite with bsize in * ||
           (rewrite substitute_topen2 by steps);
      eauto with omega.
Qed.

Lemma has_polarities_subst:
  forall T pols l,
    has_polarities T pols ->
    pclosed_mapping l type_var ->
    twfs l 0 ->
    has_polarities (psubstitute T l term_var) pols.
Proof.
  eauto using has_polarities_subst_aux.
Qed.

Lemma has_polarities_subst_erase:
  forall (X : nat) (gamma : map nat tree) (Ts : tree) (theta : interpretation) l pols,
    is_annotated_type Ts ->
    has_polarities (topen 0 Ts (fvar X type_var)) pols ->
    satisfies (reducible_values theta) (erase_context gamma) l ->
    has_polarities (topen 0 (psubstitute (erase_type Ts) l term_var) (fvar X type_var)) pols.
Proof.
  steps.
  apply has_polarities_erase in H0;
    repeat step || rewrite erase_type_topen in * by steps; eauto 2 with bannot step_tactic.
  rewrite substitute_topen2; steps; eauto with btwf.
  apply has_polarities_subst; steps; eauto with bfv btwf.
Qed.
