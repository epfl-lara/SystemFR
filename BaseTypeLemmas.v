Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.Sets.
Require Import SystemFR.ListUtils.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListLemmas.
Require Import SystemFR.TermListReducible.

Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityUnused.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.

Require Import SystemFR.SubstitutionLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.BaseType.

Require Import Omega.

Opaque reducible_values.

Lemma base_type_open:
  forall X T T0, base_type X T T0 -> forall k a,
    is_erased_term a ->
    base_type X (open k T a) (open k T0 a).
Proof.
  induction 1; repeat step || constructor || t_fv_open || t_listutils || rewrite is_erased_term_tfv in * by assumption;
    eauto with bfv;
    eauto with berased.
Qed.

Lemma base_type_erased:
  forall X T T0,
    base_type X T T0 ->
    is_erased_type T0.
Proof.
  induction 1; steps.
Qed.

Hint Resolve base_type_erased: berased.

Lemma base_type_approx_aux:
  forall n X Ts T theta l v RC,
    typeNodes T < n ->
    wfs l 0 ->
    pclosed_mapping l type_var ->
    base_type X Ts T ->
    erased_terms l ->
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
    try solve [ eapply_any; repeat step || autorewrite with bsize in *;
                eauto 1; try omega; eauto 2 using base_type_open; eauto 2 with berased ];
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
    erased_terms l ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducible_values theta v (psubstitute T l term_var).
Proof.
  intros; eauto using base_type_approx_aux.
Qed.
