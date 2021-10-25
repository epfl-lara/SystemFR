From Equations Require Import Equations.
Require Import Equations.Prop.Subterm.

Require Import Psatz.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.StrictPositivityLemma.
Require Export SystemFR.ReducibilitySubst.

Opaque makeFresh.
Opaque PeanoNat.Nat.eq_dec.
Opaque reducible_values.
Opaque strictly_positive.

Lemma strictly_positive_push_forall2:
  forall T ρ A B v X,
    ~(X ∈ pfv T type_var) ->
    non_empty ρ A ->
    twf A 0 ->
    twf B 0 ->
    twf T 1 ->
    wf A 0 ->
    wf B 1 ->
    wf T 0 ->
    is_erased_type A ->
    is_erased_type B ->
    is_erased_type T ->
    pfv A term_var = nil ->
    pfv B term_var = nil ->
    pfv T term_var = nil ->
    valid_interpretation ρ ->
    strictly_positive (topen 0 T (fvar X type_var)) (X :: nil) ->
    (forall a,
        [ ρ ⊨ a : A ]v ->
        [ ρ ⊨ v : topen 0 T (open 0 B a) ]v) ->
    [ ρ ⊨ v : topen 0 T (T_forall A B) ]v.
Proof.
  intros; instantiate_non_empty; repeat step.
  apply reducible_values_subst_head with
    (makeFresh (
       pfv T type_var ::
       pfv A type_var ::
       pfv B type_var ::
       nil
    ));
    repeat step || list_utils;
    try finisher.

  rewrite cons_app.
  match goal with
  | H: wf ?B 1 |- [ ((?X,?RC) :: nil) ++ ?ρ ⊨ ?v : ?T ]v =>
    eapply strictly_positive_push_forall with
      ((X, fun a v => [ ρ ⊨ v : open 0 B a ]v) :: nil) A
  end; eauto;
    repeat step || apply wf_topen || apply twf_topen || apply is_erased_type_topen ||
           fv_open || list_utils || apply wf_open || apply twf_open ||
           apply reducibility_is_candidate ||
           t_instantiate_reducible || apply reducible_values_subst_head2 || simp_red || t_closing;
    try finisher;
    eauto with twf;
    eauto with wf;
    eauto 2 with fv step_tactic.
  - eapply strictly_positive_rename_one; eauto; steps; try finisher.
  - rewrite (is_erased_term_tfv a0) in *; (steps; eauto with erased).
Qed.
