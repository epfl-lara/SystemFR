Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.StarInversions.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.
Require Import Termination.Syntax.
Require Import Termination.Trees.
Require Import Termination.Tactics.
Require Import Termination.Equivalence.
Require Import Termination.OpenTOpen.

Require Import Termination.SizeLemmas.

Require Import Termination.WFLemmas.
Require Import Termination.TWFLemmas.
Require Import Termination.ErasedTermLemmas.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.
Require Import Termination.ReducibilityMeasure.
Require Import Termination.ReducibilitySubst.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.ReducibilityUnused.
Require Import Termination.RedTactics2.

Require Import Termination.IdRelation.
Require Import Termination.EqualWithRelation.

Require Import Termination.EquivalentWithRelation.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.Freshness.
Require Import Termination.SwapHoles.
Require Import Termination.ListUtils.
Require Import Termination.TOpenTClose.
Require Import Termination.StrictPositivity.
Require Import Termination.StrictPositivityLemmas.
Require Import Termination.StrictPositivityLemma.

Require Import Termination.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Lemma strictly_positive_push_forall2:
  forall T theta A B v X,
    ~(X ∈ pfv T type_var) ->
    non_empty theta A ->
    twf A 0 ->
    twf B 0 ->
    twf T 1 ->
    wf A 0 ->
    wf B 1 ->
    wf T 0 ->
    is_erased_type A ->
    is_erased_type T ->
    valid_interpretation theta ->
    strictly_positive (topen 0 T (fvar X type_var)) (X :: nil) ->
    (forall a,
        reducible_values theta a A ->
        reducible_values theta v (topen 0 T (open 0 B a))) ->
    reducible_values theta v (topen 0 T (T_forall A B)).
Proof.
  intros; t_instantiate_non_empty; repeat step.
  apply reducibility_subst_head with
    (makeFresh (
       pfv T type_var ::
       pfv A type_var ::
       pfv B type_var ::
       nil
    ));
    repeat step || t_listutils;
    try finisher.

  rewrite cons_app.
  match goal with
  | H: wf ?B 1 |- reducible_values (((?X,?RC) :: nil) ++ ?theta) ?v ?T =>
    eapply strictly_positive_push_forall with
      ((X, fun a v => reducible_values theta v (open 0 B a)) :: nil) A
  end; eauto;
    repeat step || apply wf_topen || apply twf_topen || apply is_erased_type_topen ||
           t_fv_open || t_listutils || apply wf_open || apply twf_open ||
           t_instantiate_reducible || apply reducibility_subst_head2 || simp_red || t_closing;
    eauto using reducibility_is_candidate with b_valid_interp;
    try finisher;
    eauto with btwf;
    eauto with bwf.

  - eapply strictly_positive_rename_one; eauto; steps; try finisher.
  - rewrite (is_erased_term_tfv a0) in *; (steps; eauto with berased).
Qed.
