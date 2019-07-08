Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

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

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.
Require Import SystemFR.ReducibilityMeasure.
Require Import SystemFR.ReducibilitySubst.
Require Import SystemFR.ReducibilityRenaming.
Require Import SystemFR.ReducibilityUnused.
Require Import SystemFR.RedTactics2.

Require Import SystemFR.IdRelation.
Require Import SystemFR.EqualWithRelation.

Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.AssocList.
Require Import SystemFR.Sets.
Require Import SystemFR.Freshness.
Require Import SystemFR.SwapHoles.
Require Import SystemFR.ListUtils.
Require Import SystemFR.TOpenTClose.
Require Import SystemFR.StrictPositivity.
Require Import SystemFR.StrictPositivityLemmas.
Require Import SystemFR.StrictPositivityLemma.


Require Import SystemFR.FVLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Lemma cons_app:
  forall X (x: X) (xs: list X),
    x :: xs = (x :: nil) ++ xs.
Proof.
  steps.
Qed.

Lemma strictly_positive_pull_forall:
  forall T theta A B v X,
    ~(X ∈ pfv T type_var) ->
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
    reducible_values theta v (topen 0 T (T_forall A B)) ->
    forall a,
      reducible_values theta a A ->
      reducible_values theta v (topen 0 T (open 0 B a)).
Proof.
  steps.
  apply reducibility_subst_head with
    (makeFresh (
       pfv T type_var ::
       pfv A type_var ::
       pfv B type_var ::
       pfv (open 0 B a) type_var ::
       nil
    ));
    repeat step || t_listutils || apply twf_open || apply wf_open;
    try finisher;
      eauto with btwf;
      eauto with bwf;
      eauto with berased.

  rewrite cons_app.
  lazymatch goal with
  | H: wf ?B 1 |- reducible_values (((?X,?RC) :: nil) ++ ?theta) ?v ?T =>
    eapply strictly_positive_push_forall with
      ((X, fun a2 v => reducible_values theta v (T_forall A B)) :: nil) A
  end;
    repeat step || apply wf_topen || apply twf_topen || unfold non_empty ||
           apply is_erased_type_topen || t_listutils || simp_red ||
           apply reducibility_subst_head2 || t_instantiate_reducible ||
           (eapply strictly_positive_rename_one; eauto);
    eauto;
    try finisher;
    eauto using reducibility_is_candidate;
    eauto with berased.
Qed.
