Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.SizeLemmas.
Require Import Termination.Sets.
Require Import Termination.ListUtils.
Require Import Termination.ErasedTermLemmas.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityUnused.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Require Import Termination.SubstitutionLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WellFormed.

Require Import Termination.BaseType.

Require Import Omega.

Opaque reducible_values.

Lemma base_type_open:
  forall X T T0, base_type X T T0 -> forall k a,
    is_erased_term a ->
    base_type X (open k T a) (open k T0 a).
Proof.
  induction 1; repeat step || constructor || t_fv_open || t_listutils || rewrite is_erased_term_tfv in * by assumption;
    eauto with bfv.
Qed.

Lemma base_type_approx_aux:
  forall n X Ts T theta l v RC,
    size T < n ->
    wfs l 0 ->
    pclosed_mapping l type_var ->
    base_type X Ts T ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    (* RC can be instantiated by the denotation of T_rec zero T0 Ts *)
    reducible_values ((X, RC) :: theta) v (psubstitute Ts l term_var) ->
    reducible_values theta v (psubstitute T l term_var).
Proof.
  induction n; intros; try omega; inversion H2;
    repeat match goal with
    | _ =>
      step || simp_red || find_exists ||
      (rewrite substitute_open2 in * by (t_closing; eauto with bfv))
    end;
    try omega;
    try solve [ eapply_any; steps; eauto with omega ];
    try solve [ eapply_any; repeat step || autorewrite with bsize in *; eauto 1; try omega; eauto 2 using base_type_open ];
    t_closer;
    eauto 2 using reducible_values_closed with step_tactic;
    try solve [ eapply reducible_unused3; eauto 1; repeat step || rewrite fv_subst_different_tag in * by steps ].
Qed.

Lemma base_type_approx:
  forall X Ts T theta l v RC,
    (* RC can be instantiated by the denotation of T_rec zero T0 Ts *)
    reducible_values ((X, RC) :: theta) v (psubstitute Ts l term_var) ->
    wfs l 0 ->
    pclosed_mapping l type_var ->
    base_type X Ts T ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducible_values theta v (psubstitute T l term_var).
Proof.
  intros; eauto using base_type_approx_aux.
Qed.
