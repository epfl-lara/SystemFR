Require Import Equations.Equations.
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

Lemma strictly_positive_pull_forall:
  forall T ρ A B v X,
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
    pfv A term_var = nil ->
    pfv B term_var = nil ->
    pfv T term_var = nil ->
    valid_interpretation ρ ->
    strictly_positive (topen 0 T (fvar X type_var)) (X :: nil) ->
    [ ρ ⊨ v : topen 0 T (T_forall A B) ]v ->
    forall a,
      [ ρ ⊨ a : A ]v ->
      [ ρ ⊨ v : topen 0 T (open 0 B a) ]v.
Proof.
  steps.
  apply reducible_values_subst_head with
    (makeFresh (
       pfv T type_var ::
       pfv A type_var ::
       pfv B type_var ::
       pfv (open 0 B a) type_var ::
       nil
    ));
    repeat step || list_utils || apply twf_open || apply wf_open;
    try finisher;
      eauto with twf;
      eauto with wf;
      eauto with fv;
      eauto with erased.

  rewrite cons_app.
  lazymatch goal with
  | H: wf ?B 1 |- [ ((?X,?RC) :: nil) ++ ?ρ ⊨ ?v : ?T ]v =>
    eapply strictly_positive_push_forall with
      ((X, fun a2 v => [ ρ ⊨ v : T_forall A B ]v) :: nil) A
  end;
    repeat step || apply wf_topen || apply twf_topen || unfold non_empty ||
           apply is_erased_type_topen || list_utils || simp_red ||
           apply reducible_values_subst_head2 || t_instantiate_reducible ||
           apply reducibility_is_candidate ||
           (eapply strictly_positive_rename_one; eauto);
    eauto;
    try finisher;
    eauto with erased wf;
    eauto 2 with fv step_tactic;
    eauto with fv.
Qed.
