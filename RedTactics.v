Require Import Coq.Strings.String.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Freshness.
Require Import Termination.FVLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TermList.
Require Import Termination.TermListLemmas.
Require Import Termination.AssocList.
Require Import Termination.TypeErasure.
Require Import Termination.FVLemmasLists.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.
Require Import Termination.ErasedTermLemmas.
Require Import Termination.StarRelation.
Require Import Termination.SmallStep.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.

Ltac t_rewrite :=
  repeat step || t_listutils || t_fv_open || finisher;
    eauto with bwf;
    eauto with btwf;
    eauto with bfv;
    eauto with b_cmap bfv.

Ltac t_closing :=
  unfold closed_value, closed_term in *; repeat step || t_listutils;
    eauto with berased;
    eauto with bwf;
    eauto with bfv;
    eauto with values;
    eauto using is_erased_term_tfv;
    eauto using is_erased_term_twf.

Ltac t_closer := try solve [ t_closing ].

Ltac tac1 :=
  repeat step || t_listutils || finisher || apply SatCons || simp_red ||
         apply satisfies_insert || t_satisfies_nodup || t_fv_open ||
         (rewrite fv_subst_different_tag by (steps; eauto with bfv)) ||
         (rewrite substitute_nothing2 in * by t_rewrite) ||
         (rewrite substitute_open3 in * by t_rewrite) ||
         (rewrite substitute_topen3 in * by t_rewrite) ||
         (rewrite substitute_skip in * by t_rewrite) ||
         (rewrite substitute_open in * by t_rewrite) ||
         (rewrite substitute_topen in * by t_rewrite);
           t_closer;
           eauto with b_equiv;
           eauto with bwf bfv;
           eauto with btwf;
           eauto with berased;
           eauto 3 using NoDup_append with sets.

Lemma instantiate_open_reducible:
  forall theta gamma t T lterms,
    open_reducible (support theta) gamma t T ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma lterms ->
    reducible theta
              (psubstitute t lterms term_var)
              (psubstitute T lterms term_var).
Proof.
  unfold open_reducible; steps.
Qed.

Ltac find_smallstep_value :=
  match goal with
  | H: star small_step ?t ?v |- exists v, star small_step ?t v /\ _ => exists v
  | H: star small_step ?t ?v |- exists x _, _ /\ _ /\ star small_step ?t x /\ _ => exists v
  end.

Ltac find_smallstep_value2 :=
  match goal with
  | H: star small_step _ ?v |- exists v, star small_step ?t v /\ _ => exists v
  | H: star small_step _ ?v |- exists x _, _ /\ _ /\ star small_step ?t x /\ _ => exists v
  end.

Ltac find_exists :=
  match goal with
  | |- exists a b _, pp ?c ?d = pp a b /\ _ => exists c, d
  | |- (exists x, tleft ?v = tleft x /\ _) \/ _  => left; exists v
  | |- _ \/ (exists x, tright ?v = tright x /\ _)  => right; exists v
  end.

Ltac find_reducible_value :=
  match goal with
  | H: reducible_values ?theta ?v (topen 0 ?T _) |-
      exists a _, reducible_values ?theta a (topen 0 ?T _) /\ _ => exists v
  end.

Ltac reducibility_choice :=
  match goal with
  | H: reducible_values ?theta ?v (topen 0 ?T _) |-
      reducible_values ?theta ?v (topen 0 ?T _) \/ _ => left
  | H: reducible_values ?theta ?v (topen 0 ?T _) |-
      _ \/ reducible_values ?theta ?v (topen 0 ?T _) => right
  end.

Ltac t_instantiate_sat2 :=
  match goal with
  | H0: open_reducible (support ?theta) ?gamma ?t ?T,
    H1: valid_interpretation ?theta,
    H2: satisfies (reducible_values ?theta) ?gamma ?lterms
    |- _ =>
      poseNew (Mark (theta, gamma, t, T, lterms) "instantiate_open_reducible");
      unshelve epose proof (instantiate_open_reducible theta gamma t T lterms H0 H1 H2)
  end.

Ltac t_instantiate_sat3 :=
  match goal with
  | H0: forall theta lterms,
      valid_interpretation theta ->
      satisfies (reducible_values theta) ?gamma lterms ->
      support theta = support ?theta0 ->
      _,
    H1: valid_interpretation ?theta0,
    H2: satisfies (reducible_values ?theta0) ?gamma ?lterms0
    |- _ =>
      poseNew (Mark (H0, theta0, gamma, lterms0) "instantiate_open_reducible");
      pose proof (H0 theta0 lterms0 H1 H2 eq_refl)
  end.

Ltac t_instantiate_sat4 :=
  match goal with
  | H0: forall theta lterms,
      valid_interpretation theta ->
      satisfies (reducible_values theta) ?gamma lterms ->
      support theta = support _ ->
      _,
    H1: valid_interpretation ?theta0,
    H2: satisfies (reducible_values ?theta0) ?gamma ?lterms0
    |- _ =>
      poseNew (Mark (H0, theta0, gamma, lterms0) "instantiate_sat4");
      unshelve epose proof (H0 _ _ H1 H2 _)
  end.

Ltac t_instantiate_sat5 :=
  match goal with
  | H0: forall lterms theta,
      valid_interpretation theta ->
      satisfies (reducible_values theta) ?gamma lterms ->
      _,
    H1: valid_interpretation ?theta0,
    H2: satisfies (reducible_values ?theta0) ?gamma ?lterms0
    |- _ =>
      poseNew (Mark (H0, theta0, gamma, lterms0) "instantiate_open_reducible");
      pose proof (H0 lterms0 theta0 H1 H2)
  end.

Ltac t_reduces_to :=
  match goal with
  | H: reduces_to ?P ?t |- reduces_to ?P' ?t => apply (reduces_to_equiv P P' t H)
  end.

Ltac t_instantiate_reducible :=
  match goal with
  | H1: reducible_values _ ?v ?T, H2: is_erased_term ?v, H3: forall a, _ -> _ -> _ |- _ =>
    poseNew (Mark (v,H3) "t_instantiate_reducible");
    pose proof (H3 v H2 H1)
  | H1: reducible_values _ ?v ?T, H2: forall a, _ -> _ |- _ =>
    poseNew (Mark (v,H2) "t_instantiate_reducible");
    pose proof (H2 v H1)
  end.

Ltac t_instantiate_rc :=
  match goal with
  | H: reducibility_candidate ?RC, H2: forall R, reducibility_candidate R -> _ |- _ =>
     poseNew (Mark (H,H2) "instantiate_rc");
     pose proof (H2 RC H)
  end.
