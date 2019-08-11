Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.Sets.
Require Import SystemFR.Tactics.
Require Import SystemFR.Syntax.
Require Import SystemFR.TermList.
Require Import SystemFR.SmallStep.
Require Import SystemFR.AssocList.
Require Import SystemFR.EquivalenceLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.TypeErasure.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.StarInversions.
Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.TermProperties.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.SomeTerms.
Require Import SystemFR.FVLemmas.
Require Import SystemFR.TermListLemmas.
Require Import SystemFR.NatCompare.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.EqualWithRelation.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityRenaming.
Require Import SystemFR.ReducibilityUnused.
Require Import SystemFR.ReducibilitySubst.
Require Import SystemFR.RedTactics.

Require Import SystemFR.Freshness.


Require Import SystemFR.FVLemmasLists.
Require Import SystemFR.WFLemmasLists.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_rec_step:
  forall theta t1 t2 T0 Ts t,
    reducible_values theta t (T_rec t1 T0 Ts) ->
    star small_step t1 t2 ->
    reducible_values theta t (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with berased.
  - left; exists v'; steps; eapply star_many_steps; eauto; unfold irred; repeat step || t_invert_step.
  - right. unshelve eexists n', v', X, _, _; steps;
             eauto using is_nat_value_value, value_irred, star_many_steps with values.
Qed.

Lemma reducible_values_rec_backstep:
  forall theta t1 t2 T0 Ts t,
    reducible_values theta t (T_rec t1 T0 Ts) ->
    is_erased_term t2 ->
    star small_step t2 t1 ->
    reducible_values theta t (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with berased.
  - left; steps; eauto using star_smallstep_trans.
  - right. unshelve eexists n', v', X, _, _; steps; eauto using star_smallstep_trans.
Qed.

Lemma reducible_values_rec_equivalent:
  forall theta t1 t2 T0 Ts t,
    reducible_values theta t (T_rec t1 T0 Ts) ->
    equivalent t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    reducible_values theta t (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with berased.
  - left; eauto using equivalence_def with values.
  - right. unshelve eexists n', v', X, _, _; steps;
             eauto using equivalence_def with values.
Qed.

Lemma reducible_rec_equivalent:
  forall theta t1 t2 T0 Ts t,
    reducible theta t (T_rec t1 T0 Ts) ->
    valid_interpretation theta ->
    equivalent t1 t2 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    reducible theta t (T_rec t2 T0 Ts).
Proof.
  eauto using reducible_values_rec_equivalent, reducible_values_exprs.
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

Lemma reducible_values_unfold:
  forall theta v n T0 Ts,
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
    reducible_values theta (notype_tfold v) (T_rec (succ n) T0 Ts) ->
    reducible_values theta v (topen 0 Ts (T_rec n T0 Ts)).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | H: star small_step (succ _) ?v |- _ =>
              poseNew (Mark 0 "inv succ");
              unshelve epose proof (star_smallstep_succ_inv _ v H _ _ eq_refl)
           | _ => step || simp_red || step_inversion is_value
           end; eauto with values.

  eapply reducibility_subst_head; eauto; repeat step || t_listutils;
    try solve [ rewrite is_erased_term_tfv in *; steps ].
  eapply reducible_rename_one_rc; eauto using reducibility_is_candidate.
  apply equivalent_rc_sym; apply equivalent_rc_rec_step; eauto with berased.
Qed.

Lemma red_one:
  forall theta, reducible_values theta (succ zero) T_nat.
Proof.
  repeat step || simp_red.
Qed.

Ltac inst_one :=
  match goal with
  | H: forall a, reducible_values ?theta _ T_nat -> _ |- _ =>
      poseNew (Mark 0 "once"); unshelve epose proof (H (succ zero) (red_one theta))
  end.

Lemma fold_in_rec:
  forall theta v T0 Ts n,
    valid_interpretation theta ->
    reducible_values theta v (T_rec n T0 Ts) ->
    exists v', closed_value v' /\ v = notype_tfold v'.
Proof.
  repeat match goal with
         | _ => step || simp_red || inst_one
         | H: reducible_values ?theta ?v ?T |- _ => apply reducible_values_closed with theta T
         | H: reducible_values ?theta ?v ?T |- _ => exists v
         | H: star small_step (succ ?n) zero |- _ =>
             unshelve eapply (False_ind _ (smallstep_succ_zero (succ n) zero H n _ _))
         end; eauto using reducibility_is_candidate.
Qed.

Lemma star_unfold_fold:
  forall t v,
    closed_value (notype_tfold v) ->
    star small_step t (notype_tfold v) ->
    star small_step (tunfold t) v.
Proof.
  unfold closed_value.
  repeat step || step_inversion is_value.
  eapply star_smallstep_trans; eauto with bsteplemmas; eauto with smallstep.
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
           | _ => apply star_unfold_fold
           | _ => apply reducible_values_unfold
           | H: star small_step ?t (notype_tfold ?v) |- exists t', star small_step (tunfold ?t) _ /\ _ => exists v
           | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?v (T_rec _ _ _) |- _ =>
               poseNew (Mark 0 "once");
               is_var v; unshelve epose proof (fold_in_rec _ _ _ _ _ H1 H2)
           | _ => step || unfold closed_value in *
           end; eauto with values.
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

Lemma spos_succ_pred:
  forall (n : tree) v (lterms : list (nat * tree)),
    is_nat_value v ->
    star small_step n v ->
    equivalent (spositive n) ttrue ->
    equivalent n (succ (tmatch n notype_err (lvar 0 term_var))).
Proof.
  unfold equivalent; unfold spositive;
    repeat match goal with
           | H: forall v, is_value v -> star small_step ttrue v ->  _ |- _ =>
               unshelve epose proof (H ttrue _ _); clear H
           | _ => step || t_invert_step || t_invert_star || t_nostep || t_deterministic_star || step_inversion is_value
           | _ => apply star_smallstep_succ
           | H2: star small_step (tmatch ?tn _ _) ?v,
             H3: star small_step ?tn zero |- _ =>
             poseNew (Mark H2 "inv match zero");
             unshelve epose proof (star_smallstep_match_zero _ v H2 _ _ _ _ eq_refl H3)
           | H2: star small_step (tmatch _ _ _) ?v |- _ =>
             poseNew (Mark H2 "inv match");
             unshelve epose proof (star_smallstep_match_inv _ v H2 _ _ _ _ eq_refl)
           end;
  eauto using star_smallstep_trans with bsteplemmas smallstep.
Qed.

Lemma reducible_trec:
  forall theta v n T0 Ts,
    reducible theta v (T_rec n T0 Ts) ->
    exists v', is_nat_value v' /\ star small_step n v'.
Proof.
  unfold reducible, reduces_to; repeat step || simp_red.
  - exists zero; steps.
  - exists (succ n'); steps; eauto with b_inv.
Qed.

Ltac t_reducible_trec :=
  match goal with
  | H: reducible _ _ (T_rec _ _ _) |- _ =>
    poseNew (Mark H "reducible_trec");
    pose proof (reducible_trec _ _ _ _ _ H)
  end.

Lemma open_reducible_unfold2:
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
    (forall theta l,
       valid_interpretation theta ->
       satisfies (reducible_values theta) gamma l ->
       support theta = tvars ->
       equivalent (spositive (psubstitute n l term_var)) ttrue) ->
    open_reducible tvars gamma t (T_rec n T0 Ts) ->
    open_reducible tvars gamma (tunfold t) (topen 0 Ts (T_rec (notype_tpred n) T0 Ts)).
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen || t_instantiate_sat3 || t_reducible_trec;
      eauto with btwf.

  apply reducible_unfold; steps; eauto with bwf btwf berased.

  eapply reducible_rec_equivalent; steps;
    eauto with berased;
    eauto using spos_succ_pred.
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
    reducible theta (notype_tfold t) (T_rec (succ n) T0 Ts).
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
    open_reducible tvars gamma (notype_tfold t) (T_rec (succ n) T0 Ts).
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

Lemma reducible_unfold_zero:
  forall theta t T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    reducible theta t (T_rec zero T0 Ts) ->
    reducible theta (tunfold t) T0.
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | _ => apply star_unfold_fold
           | _ => apply reducible_values_unfold
           | H: star small_step ?t (notype_tfold ?v) |- exists t', star small_step (tunfold ?t) _ /\ _ => exists v
           | H1: valid_interpretation ?theta, H2: reducible_values ?theta ?v (T_rec _ _ _) |- _ =>
               poseNew (Mark 0 "once");
               is_var v; unshelve epose proof (fold_in_rec _ _ _ _ _ H1 H2)
           | _ => step || unfold closed_value in * || simp_red || t_invert_star
           end; eauto with values.
Qed.

Lemma open_reducible_unfold_zero:
  forall tvars gamma t T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    open_reducible tvars gamma t (T_rec zero T0 Ts) ->
    open_reducible tvars gamma (tunfold t) T0.
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
      eauto with btwf.

  eapply reducible_unfold_zero; steps;
    eauto with bwf btwf berased.
Qed.

Lemma open_reducible_unfold_zero2:
  forall tvars gamma t T0 Ts n,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    (forall theta l,
       valid_interpretation theta ->
       satisfies (reducible_values theta) gamma l ->
       support theta = tvars ->
       equivalent (substitute n l) zero) ->
    open_reducible tvars gamma t (T_rec n T0 Ts) ->
    open_reducible tvars gamma (tunfold t) T0.
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || rewrite substitute_topen;
      eauto with btwf.

  apply reducible_unfold_zero with (psubstitute Ts lterms term_var); steps;
    eauto with bwf btwf berased.

  apply reducible_rec_equivalent with (psubstitute n lterms term_var); steps;
    eauto with berased.
Qed.

Lemma reducible_fold_zero:
  forall theta t T0 Ts,
    valid_interpretation theta ->
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    reducible theta t T0 ->
    reducible theta (notype_tfold t) (T_rec zero T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | _ => step || simp_red
           end; eauto with values.

  eexists; steps; eauto with bsteplemmas.
  repeat step || simp_red; t_closer; eauto with smallstep.
Qed.

Lemma open_reducible_fold_zero:
  forall tvars gamma t T0 Ts,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    open_reducible tvars gamma t T0 ->
    open_reducible tvars gamma (notype_tfold t) (T_rec zero T0 Ts).
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  apply reducible_fold_zero; steps;
    eauto with bwf;
    eauto 3 with btwf;
    eauto with berased.
Qed.

Lemma open_reducible_fold2:
  forall tvars gamma t n T0 Ts p pn,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    ~(p ∈ pfv n term_var) ->
    ~(p ∈ pfv_context gamma term_var) ->
    ~(p ∈ pfv t term_var) ->
    ~(p ∈ pfv T0 term_var) ->
    ~(p ∈ pfv Ts term_var) ->
    ~(pn ∈ pfv n term_var) ->
    ~(pn ∈ pfv_context gamma term_var) ->
    ~(pn ∈ pfv t term_var) ->
    ~(pn ∈ pfv T0 term_var) ->
    ~(pn ∈ pfv Ts term_var) ->
    ~(p = pn) ->
    open_reducible tvars gamma n T_nat ->
    open_reducible tvars ((p, T_equal n zero) :: gamma) t T0 ->
    open_reducible tvars
                   ((p, T_equal n (succ (fvar pn term_var))) :: (pn, T_nat) :: gamma)
                   t
                   (topen 0 Ts (T_rec (fvar pn term_var) T0 Ts)) ->
    open_reducible tvars gamma (notype_tfold t) (T_rec n T0 Ts).
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  unfold reducible, reduces_to in H21; repeat step || simp_red.

  t_invert_nat_value; steps.

  - apply reducible_rec_equivalent with zero; eauto using equivalent_sym with b_equiv; t_closing.
    apply reducible_fold_zero; steps; eauto with bwf btwf berased.
    unshelve epose proof (H17 theta ((p, uu) :: lterms) _ _ _);
      repeat tac1 || step_inversion NoDup || rewrite substitute_open in * || apply_any.

  - apply reducible_rec_equivalent with (succ v); eauto using equivalent_sym with b_equiv; t_closing.
    apply reducible_fold; steps;
      eauto with bwf;
      eauto 3 with btwf;
      eauto with berased;
      try solve [ unfold reducible, reduces_to; repeat step || simp_red || eexists; try t_closing; eauto with smallstep ].
    unshelve epose proof (H18 theta ((p, uu) :: (pn, v) :: lterms) _ _ _);
      repeat tac1 || step_inversion NoDup || rewrite substitute_open in *.
Qed.

Lemma equivalent_tpred:
  forall n n',
    star small_step n (succ n') ->
    equivalent n' (notype_tpred n).
Proof.
  unfold equivalent, notype_tpred; repeat step || t_invert_star || step_inversion is_value.
  - assert (star small_step (succ n') (succ v)); eauto using star_many_steps, value_irred with values.
    assert (is_value (succ v)); repeat step || t_invert_star; eauto with values.
  - eapply star_smallstep_trans; eauto with bsteplemmas.
    eapply star_smallstep_trans; eauto with bsteplemmas.
    eauto with smallstep.
Qed.

Lemma reducible_unfold_in:
  forall (t1 t2 T n T0 Ts : tree) (theta : interpretation),
    reducible theta t1 (T_rec n T0 Ts) ->
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf t2 1 ->
    wf n 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    (forall v,
        reducible_values theta v T0 ->
        equivalent t1 (notype_tfold v) ->
        equivalent n zero ->
        reducible theta (open 0 t2 v) T) ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ->
        equivalent t1 (notype_tfold v) ->
        reducible theta (open 0 t2 v) T) ->
    reducible theta (tunfold_in t1 t2) T.
Proof.
  intros.
  unfold reducible, reduces_to in H; steps.
  eapply star_backstep_reducible; eauto with bsteplemmas; repeat step || t_listutils;
    eauto with bwf.

  simp_red; steps.
  - apply backstep_reducible with (open 0 t2 v'); repeat step || t_listutils;
      eauto using red_is_val with smallstep;
      eauto with bwf;
      eauto with bfv;
      eauto with berased.

    apply H14; steps; eauto with b_equiv.
  - apply (
        reducible_rename_one_rc
          _
          (fun t => reducible_values theta t (T_rec (notype_tpred n) T0 Ts))
          _ _ _ X X
     ) in H24;
      eauto with values;
      eauto using reducibility_is_candidate.
    + apply reducibility_subst_head in H24;
        repeat step || t_listutils || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with berased);
      eauto with bwf btwf bfv.

      apply backstep_reducible with (open 0 t2 v'); repeat step || t_listutils;
        eauto using red_is_val with smallstep;
        eauto with bwf;
        eauto with bfv;
        eauto with berased.

      apply H15; steps; eauto with b_equiv.

    + apply equivalent_rc_sym.
      apply equivalent_rc_rec_step; unfold notype_tpred; steps.
      eapply star_smallstep_trans; eauto with bsteplemmas.
      eapply Trans; eauto with smallstep values.
Qed.

Lemma open_reducible_unfold_in:
  forall tvars gamma t1 t2 T n T0 Ts p1 p2 y,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf t2 1 ->
    wf n 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (pfv t1 term_var) (support gamma) ->
    subset (pfv t2 term_var) (support gamma) ->
    ~(p1 ∈ tvars) ->
    ~(p1 ∈ pfv_context gamma term_var) ->
    ~(p1 ∈ support gamma) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(p2 ∈ tvars) ->
    ~(p2 ∈ pfv_context gamma term_var) ->
    ~(p2 ∈ support gamma) ->
    ~(p2 ∈ fv t1) ->
    ~(p2 ∈ fv t2) ->
    ~(p2 ∈ fv n) ->
    ~(p2 ∈ fv T0) ->
    ~(p2 ∈ fv Ts) ->
    ~(p2 ∈ fv T) ->
    ~(y ∈ tvars) ->
    ~(y ∈ pfv_context gamma term_var) ->
    ~(y ∈ support gamma) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    NoDup (p1 :: p2 :: y :: nil) ->
    open_reducible tvars gamma t1 (T_rec n T0 Ts) ->
    open_reducible tvars
             ((p2, T_equal n zero) :: (p1, T_equal t1 (notype_tfold (fvar y term_var))) :: (y, T0) :: gamma)
             (open 0 t2 (fvar y term_var)) T ->
    open_reducible tvars
             ((p1, T_equal t1 (notype_tfold (fvar y term_var))) ::
              (y, topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ::
              gamma)
             (open 0 t2 (fvar y term_var)) T ->
    open_reducible tvars gamma (tunfold_in t1 t2) T.
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_reducible_trec.

  eapply reducible_unfold_in; try eassumption;
    steps;
    eauto with bwf;
    eauto with btwf;
    eauto with bfv;
    eauto with berased.

  - unshelve epose proof (H42 theta ((p2, uu) :: (p1, uu) :: (y, v) :: lterms) _ _ _);
      repeat step_inversion NoDup || tac1.
  - unshelve epose proof (H43 theta ((p1, uu) :: (y, v) :: lterms) _ _ _);
      repeat match goal with
             | |- reducible_values _ _ T_nat => simp reducible_values
             | |- reducible_values _ _ (T_equal _ _) => simp reducible_values
             | _ => step_inversion NoDup || tac0
             end.
Qed.

Lemma equivalent_zero_contradiction:
  forall n,
    equivalent (tlt zero n) ttrue ->
    star small_step n zero ->
    False.
Proof.
  intros.
  apply (equivalent_tlt_steps _ _ zero zero) in H;
    steps.
  apply equivalent_true in H.
  apply tlt_sound in H; steps; eauto with omega.
Qed.

Lemma reducible_unfold_pos_in:
  forall (t1 t2 T n T0 Ts : tree) (theta : interpretation),
    reducible theta t1 (T_rec n T0 Ts) ->
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf t2 1 ->
    wf n 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation theta ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    equivalent (tlt zero n) ttrue ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ->
        equivalent t1 (notype_tfold v) ->
        reducible theta (open 0 t2 v) T) ->
    reducible theta (tunfold_in t1 t2) T.
Proof.
  intros.
  unfold reducible, reduces_to in H; steps.
  eapply star_backstep_reducible; eauto with bsteplemmas; repeat step || t_listutils;
    eauto with bwf.

  simp_red; steps; eauto using equivalent_zero_contradiction with falsity.

  - apply (
        reducible_rename_one_rc
          _
          (fun t => reducible_values theta t (T_rec (notype_tpred n) T0 Ts))
          _ _ _ X X
     ) in H24;
      eauto with values;
      eauto using reducibility_is_candidate.
    + apply reducibility_subst_head in H24;
        repeat step || t_listutils || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with berased);
      eauto with bwf btwf bfv.

      apply backstep_reducible with (open 0 t2 v'); repeat step || t_listutils;
        eauto using red_is_val with smallstep;
        eauto with bwf;
        eauto with bfv;
        eauto with berased.

      apply H15; steps; eauto with b_equiv.

    + apply equivalent_rc_sym.
      apply equivalent_rc_rec_step; unfold notype_tpred; steps.
      eapply star_smallstep_trans; eauto with bsteplemmas.
      eapply Trans; eauto with smallstep values.
Qed.

Lemma open_reducible_unfold_pos_in:
  forall tvars gamma t1 t2 T n T0 Ts p1 y,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    wf t1 0 ->
    wf t2 1 ->
    wf n 0 ->
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (pfv t1 term_var) (support gamma) ->
    subset (pfv t2 term_var) (support gamma) ->
    ~(p1 ∈ tvars) ->
    ~(p1 ∈ pfv_context gamma term_var) ->
    ~(p1 ∈ support gamma) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(y ∈ tvars) ->
    ~(y ∈ pfv_context gamma term_var) ->
    ~(y ∈ support gamma) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    NoDup (p1 :: y :: nil) ->
    open_reducible tvars gamma t1 (T_rec n T0 Ts) ->
    (forall theta l,
      valid_interpretation theta ->
      satisfies (reducible_values theta) gamma l ->
      support theta = tvars ->
      equivalent (substitute (tlt zero n) l) ttrue) ->
    open_reducible
      tvars
      ((p1, T_equal t1 (notype_tfold (fvar y term_var))) ::
       (y, topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ::
       gamma)
      (open 0 t2 (fvar y term_var)) T ->
    open_reducible tvars gamma (tunfold_in t1 t2) T.
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_reducible_trec.

  eapply reducible_unfold_pos_in; try eassumption;
    steps;
    eauto with bwf;
    eauto with btwf;
    eauto with bfv;
    eauto with berased.

  - unshelve epose proof (H34 theta ((p1, uu) :: (y, v) :: lterms) _ _ _);
      repeat match goal with
             | |- reducible_values _ _ T_nat => simp reducible_values
             | |- reducible_values _ _ (T_equal _ _) => simp reducible_values
             | _ => step_inversion NoDup || tac0
             end.
Qed.
