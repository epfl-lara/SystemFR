Require Import Coq.Lists.List.

Require Import Termination.Sets.
Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.TermList.
Require Import Termination.SmallStep.
Require Import Termination.AssocList.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.StarRelation.
Require Import Termination.SizeLemmas.
Require Import Termination.StarLemmas.
Require Import Termination.TypeErasure.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.
Require Import Termination.StarInversions.
Require Import Termination.EquivalentWithRelation.
Require Import Termination.EqualWithRelation.
Require Import Termination.TermProperties.
Require Import Termination.ErasedTermLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityRenaming.
Require Import Termination.ReducibilityUnused.
Require Import Termination.ReducibilitySubst.
Require Import Termination.RedTactics.

Require Import Termination.Freshness.

Require Import Termination.FVLemmasLists.
Require Import Termination.WFLemmasLists.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_rec_step:
  forall theta t1 t2 T0 Ts t,
    star small_step t1 t2 ->
    reducible_values theta t (T_rec t1 T0 Ts) ->
    reducible_values theta t (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with berased.
  - left; steps; eapply star_many_steps; eauto; unfold irred; repeat step || t_invert_step.
  - right. unshelve eexists n', v', X, _, _; steps;
             eauto using is_nat_value_value, value_irred, star_many_steps.
Qed.

Lemma reducible_values_rec_backstep:
  forall theta t1 t2 T0 Ts t,
    is_erased_term t2 ->
    star small_step t2 t1 ->
    reducible_values theta t (T_rec t1 T0 Ts) ->
    reducible_values theta t (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with berased.
  - left; steps; eauto using star_smallstep_trans.
  - right. unshelve eexists n', v', X, _, _; steps; eauto using star_smallstep_trans.
Qed.

Lemma reducible_values_rec_equivalent:
  forall theta t1 t2 T0 Ts t,
    equivalent t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    reducible_values theta t (T_rec t1 T0 Ts) ->
    reducible_values theta t (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with berased.
  - left; eauto using equivalence_def with values.
  - right. unshelve eexists n', v', X, _, _; steps;
             eauto using equivalence_def with values.
Qed.

Lemma equivalent_rc_rec_step:
  forall theta t1 t2 T0 Ts,
    is_erased_term t1 ->
    star small_step t1 t2 ->
    equivalent_rc
      (fun t => reducible_values theta t (T_rec t1 T0 Ts))
      (fun t => reducible_values theta t (T_rec t2 T0 Ts)).
Proof.
  unfold equivalent_rc; steps;
    eauto using reducible_values_rec_step, reducible_values_rec_backstep.
Qed.

Lemma reducible_unfold:
  forall theta t n T0 Ts,
    wf n 0 ->
    twf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    reducible theta t (T_rec (succ n) T0 Ts) ->
    reducible theta (tunfold t) (topen 0 Ts (T_rec n T0 Ts)).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | H: star small_step (succ _) ?v |- _ =>
              poseNew (Mark 0 "inv succ");
              unshelve epose proof (star_smallstep_succ_inv _ v H _ _ eq_refl)
           | _ => step || simp_red || step_inversion is_value
           end; eauto with values.

  exists v'; steps.
  - apply star_smallstep_trans with (tunfold (tfold v'));
      eauto with bsteplemmas.
    eapply Trans; eauto with smallstep.
    apply SPBetaFold; unshelve eapply (red_is_val _ _ _ _ H20); steps;
      eauto using reducibility_is_candidate.

  - eapply reducibility_subst_head; eauto; repeat step || t_listutils;
      try solve [ rewrite is_erased_term_tfv in *; steps ].
    eapply reducible_rename_one_rc; eauto using reducibility_is_candidate.
    apply equivalent_rc_sym; apply equivalent_rc_rec_step; eauto with berased.
Qed.

Lemma open_reducible_unfold:
  forall tvars gamma t n T0 Ts,
    wf n 0 ->
    twf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    open_reducible tvars gamma t (T_rec (succ n) T0 Ts) ->
    open_reducible tvars gamma (tunfold t) (topen 0 Ts (T_rec n T0 Ts)).
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
      eauto with btwf.

  apply reducible_unfold; steps;
    eauto with bwf btwf berased.
Qed.

Lemma reducible_fold:
  forall theta t n T0 Ts,
    valid_interpretation theta ->
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    reducible theta n T_nat ->
    reducible theta t (topen 0 Ts (T_rec n T0 Ts)) ->
    reducible theta (tfold t) (T_rec (succ n) T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | _ => step || simp_red
           end; eauto with values.

  eexists; steps; eauto with bsteplemmas.
  repeat step || simp_red; t_closer.

  right.
  unshelve eexists t'0, t', (makeFresh (pfv n type_var :: pfv t'0 type_var :: pfv T0 type_var :: pfv Ts type_var :: support theta :: nil)), _, _;
    repeat step;
    try finisher;
    eauto with bsteplemmas.

  match goal with
  | |- reducible_values ((?M,_) :: _) _ _ =>
    eapply (reducible_rename_one_rc (fun v : tree => reducible_values theta v (T_rec n T0 Ts)) _ _ _ _ M M);
    repeat step || apply equivalent_rc_rec_step
  end;
    try finisher; t_closer;
    eauto using reducibility_is_candidate.

  apply reducibility_subst_head2; repeat step || t_listutils;
    try finisher;
    t_closer.
Qed.

Lemma open_reducible_fold:
  forall tvars gamma t n T0 Ts,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    open_reducible tvars gamma n T_nat ->
    open_reducible tvars gamma t (topen 0 Ts (T_rec n T0 Ts)) ->
    open_reducible tvars gamma (tfold t) (T_rec (succ n) T0 Ts).
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  apply reducible_fold; steps;
    eauto with bwf;
    eauto 3 with btwf;
    eauto with berased.

  rewrite substitute_topen in *; steps;
    eauto with btwf.
Qed.
