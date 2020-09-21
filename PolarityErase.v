Require Import Equations.Equations.

Require Import Psatz.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.OpenTOpen.
Require Export SystemFR.EqualWithRelation.
Require Export SystemFR.ReducibilityCandidate.
Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.NoTypeFVar.
Require Export SystemFR.PolarityLemmas.
Require Export SystemFR.FVLemmasLists.
Require Export SystemFR.NoTypeFVarLemmas.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.AnnotatedTermLemmas.

Opaque makeFresh.
Opaque PeanoNat.Nat.eq_dec.

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
    type_nodes T < n ->
    is_annotated_type T ->
    has_polarities T pols ->
    has_polarities (erase_type T) pols.
Proof.
  induction n; destruct T; steps; try lia;
    repeat
      step || step_inversion has_polarities || constructor || exists X || t_fv_erase ||
      rewrite <- erase_type_topen2 || apply_any || autorewrite with bsize in *;
        eauto with lia;
        eauto 2 with annot step_tactic.
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
    type_nodes T < n ->
    has_polarities T pols ->
    pclosed_mapping l type_var ->
    twfs l 0 ->
    has_polarities (psubstitute T l term_var) pols.
Proof.
  induction n; destruct T;
    repeat step || constructor || step_inversion has_polarities || exists X || t_pfv_in_subst || eapply_any ||
           autorewrite with bsize in * ||
           (rewrite substitute_topen2 by steps);
      eauto with lia.
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
  forall (X : nat) (Γ : map nat tree) (Ts : tree) (ρ : interpretation) l pols,
    is_annotated_type Ts ->
    has_polarities (topen 0 Ts (fvar X type_var)) pols ->
    satisfies (reducible_values ρ) (erase_context Γ) l ->
    has_polarities (topen 0 (psubstitute (erase_type Ts) l term_var) (fvar X type_var)) pols.
Proof.
  steps.
  apply has_polarities_erase in H0;
    repeat step || rewrite erase_type_topen in * by steps; eauto 2 with annot step_tactic.
  rewrite substitute_topen2; steps; eauto with twf.
  apply has_polarities_subst; steps; eauto with fv twf.
Qed.
