Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.StarInversions.
Require Export SystemFR.RelationClosures.
Require Export SystemFR.SmallStep.
Require Export SystemFR.Syntax.
Require Export SystemFR.Trees.
Require Export SystemFR.Tactics.
Require Export SystemFR.Equivalence.
Require Export SystemFR.OpenTOpen.

Require Export SystemFR.SizeLemmas.

Require Export SystemFR.WFLemmas.
Require Export SystemFR.TWFLemmas.
Require Export SystemFR.ErasedTermLemmas.

Require Export SystemFR.ReducibilityMeasure.
Require Export SystemFR.ReducibilitySubst.
Require Export SystemFR.ReducibilityRenaming.
Require Export SystemFR.ReducibilityUnused.
Require Export SystemFR.RedTactics2.

Require Export SystemFR.IdRelation.
Require Export SystemFR.EqualWithRelation.

Require Export SystemFR.EquivalentWithRelation.
Require Export SystemFR.AssocList.

Require Export SystemFR.Freshness.

Require Export SystemFR.ListUtils.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.StrictPositivity.
Require Export SystemFR.StrictPositivityLemmas.
Require Export SystemFR.StrictPositivityLemma.


Require Export SystemFR.FVLemmas.

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
    is_erased_type B ->
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
    eauto with wf.

  - eapply strictly_positive_rename_one; eauto; steps; try finisher.
  - rewrite (is_erased_term_tfv a0) in *; (steps; eauto with erased).
Qed.
