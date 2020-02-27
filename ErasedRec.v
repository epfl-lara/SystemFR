Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilitySubst.
Require Export SystemFR.SomeTerms.
Require Export SystemFR.NatLessThan.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_rec_step:
  forall theta t1 t2 T0 Ts v,
    reducible_values theta v (T_rec t1 T0 Ts) ->
    star scbv_step t1 t2 ->
    reducible_values theta v (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with erased.
  - left; steps; eapply star_many_steps; eauto; unfold irred; repeat step || t_invert_step.
  - right. unshelve eexists n', X, _, _; steps;
             eauto using is_nat_value_value, value_irred, star_many_steps with values.
Qed.

Lemma reducible_values_rec_backstep:
  forall theta t1 t2 T0 Ts v,
    reducible_values theta v (T_rec t1 T0 Ts) ->
    is_erased_term t2 ->
    star scbv_step t2 t1 ->
    reducible_values theta v (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with erased.
  - left; steps; eauto using star_trans.
  - right. unshelve eexists n', X, _, _; steps; eauto using star_trans.
Qed.

Lemma reducible_values_rec_equivalent:
  forall theta t1 t2 T0 Ts v,
    reducible_values theta v (T_rec t1 T0 Ts) ->
    equivalent_terms t1 t2 ->
    reducible_values theta v (T_rec t2 T0 Ts).
Proof.
  repeat step || simp_red;
    eauto with erased;
    try solve [ unfold equivalent_terms in *; steps ].
  - left; steps; eauto using equivalent_star_nat, INVZero.
  - right; unshelve eexists n', X, _, _; steps; eauto using equivalent_star_nat, INVSucc.
Qed.

Lemma reducible_rec_equivalent:
  forall theta t1 t2 T0 Ts t,
    reducible theta t (T_rec t1 T0 Ts) ->
    valid_interpretation theta ->
    equivalent_terms t1 t2 ->
    reducible theta t (T_rec t2 T0 Ts).
Proof.
  eauto using reducible_values_rec_equivalent, reducible_values_exprs.
Qed.

Lemma equivalent_rc_rec_step:
  forall theta t1 t2 T0 Ts,
    is_erased_term t1 ->
    star scbv_step t1 t2 ->
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
    pfv n term_var = nil ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    valid_interpretation theta ->
    reducible_values theta v (T_rec (succ n) T0 Ts) ->
    reducible_values theta v (topen 0 Ts (T_rec n T0 Ts)).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | H: star scbv_step (succ _) ?v |- _ =>
              poseNew (Mark 0 "inv succ");
              unshelve epose proof (star_smallstep_succ_inv _ v H _ _ eq_refl)
           | _ => step || simp_red || step_inversion cbv_value
           end; eauto with values.

  eapply reducible_values_subst_head; eauto; repeat step || list_utils;
    try solve [ rewrite is_erased_term_tfv in *; steps ].
  eapply reducible_rename_one_rc; eauto using reducibility_is_candidate.
  apply equivalent_rc_sym; apply equivalent_rc_rec_step; eauto with erased.
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
    pfv n term_var = nil ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    valid_interpretation theta ->
    reducible theta t (T_rec (succ n) T0 Ts) ->
    reducible theta t (topen 0 Ts (T_rec n T0 Ts)).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | _ => find_smallstep_value
           | _ => apply reducible_values_unfold
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
    subset (fv n) (support gamma) ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    [ tvars; gamma ⊨ t : T_rec (succ n) T0 Ts ] ->
    [ tvars; gamma ⊨ t : topen 0 Ts (T_rec n T0 Ts) ].
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
      eauto with twf.

  apply reducible_unfold; steps;
    eauto with wf twf erased fv.
Qed.

Lemma spos_succ_pred:
  forall (n : tree) v (lterms : list (nat * tree)),
    is_nat_value v ->
    star scbv_step n v ->
    equivalent_terms (spositive n) ttrue ->
    equivalent_terms n (succ (tmatch n notype_err (lvar 0 term_var))).
Proof.
  intros.
  apply equivalent_sym.
  apply equivalent_trans with v.

  - apply equivalent_star; steps;
      try solve [ top_level_unfold equivalent_terms; steps ].
    apply_anywhere equivalent_true.
    unfold spositive in *;
      repeat step || t_invert_star || t_deterministic_star.
    eapply star_trans; eauto with cbvlemmas.
    eapply Trans; eauto with smallstep; steps.

  - apply equivalent_sym.
    apply equivalent_star; steps;
      try solve [ top_level_unfold equivalent_terms; repeat step || list_utils ].
Qed.

Lemma reducible_trec:
  forall theta v n T0 Ts,
    reducible theta v (T_rec n T0 Ts) ->
    exists v', is_nat_value v' /\ star scbv_step n v'.
Proof.
  unfold reducible, reduces_to; repeat step || simp_red.
  - exists zero; steps.
  - exists (succ n'); steps; eauto with is_nat_value.
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
    subset (fv n) (support gamma) ->
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    (forall theta l,
       valid_interpretation theta ->
       satisfies (reducible_values theta) gamma l ->
       support theta = tvars ->
       equivalent_terms (spositive (psubstitute n l term_var)) ttrue) ->
    [ tvars; gamma ⊨ t : T_rec n T0 Ts ] ->
    [ tvars; gamma ⊨ t : topen 0 Ts (T_rec (notype_tpred n) T0 Ts) ].
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen || t_instantiate_sat3 || t_reducible_trec;
      eauto with twf.

  apply reducible_unfold; repeat step || list_utils; eauto with wf twf fv erased.

  eapply reducible_rec_equivalent; steps;
    eauto with erased;
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
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    reducible theta n T_nat ->
    reducible theta t (topen 0 Ts (T_rec n T0 Ts)) ->
    reducible theta t (T_rec (succ n) T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | _ => step || simp_red
           end; eauto with values.

  eexists; steps; eauto with cbvlemmas.
  repeat step || simp_red; t_closer.

  right.
  unshelve eexists v0, (makeFresh (pfv n type_var :: pfv v0 type_var :: pfv T0 type_var :: pfv Ts type_var :: support theta :: nil)), _, _;
    repeat step;
    try finisher;
    eauto with cbvlemmas.

  match goal with
  | |- reducible_values ((?M,_) :: _) _ _ =>
    eapply (reducible_rename_one_rc (fun v : tree => reducible_values theta v (T_rec n T0 Ts)) _ _ _ _ M M);
    repeat step || apply equivalent_rc_rec_step
  end;
    try finisher; t_closer;
    eauto using reducibility_is_candidate.

  apply reducible_values_subst_head2; repeat step || list_utils;
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
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    [ tvars; gamma ⊨ n : T_nat ] ->
    [ tvars; gamma ⊨ t : topen 0 Ts (T_rec n T0 Ts) ] ->
    [ tvars; gamma ⊨ t : T_rec (succ n) T0 Ts ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  apply reducible_fold; steps;
    eauto with wf;
    eauto with fv;
    eauto 3 with twf;
    eauto with erased.

  rewrite substitute_topen in *; steps;
    eauto with twf.
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
    reducible theta t T0.
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | _ => apply reducible_values_unfold
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
    [ tvars; gamma ⊨ t : T_rec zero T0 Ts ] ->
    [ tvars; gamma ⊨ t : T0 ].
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
      eauto with twf.

  eapply reducible_unfold_zero; steps;
    eauto with wf twf erased.
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
       equivalent_terms (substitute n l) zero) ->
    [ tvars; gamma ⊨ t : T_rec n T0 Ts ] ->
    [ tvars; gamma ⊨ t : T0 ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || rewrite substitute_topen;
      eauto with twf.

  apply reducible_unfold_zero with (psubstitute Ts lterms term_var); steps;
    eauto with wf twf erased.

  apply reducible_rec_equivalent with (psubstitute n lterms term_var); steps;
    eauto with erased.
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
    reducible theta t (T_rec zero T0 Ts).
Proof.
  unfold reducible, reduces_to;
    repeat match goal with
           | _ => step || simp_red
           end; eauto with values.

  eexists; steps; eauto with cbvlemmas.
  repeat step || simp_red; t_closer; eauto with star.
Qed.

Lemma open_reducible_fold_zero:
  forall tvars gamma t T0 Ts,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    [ tvars; gamma ⊨ t : T0 ] ->
    [ tvars; gamma ⊨ t : T_rec zero T0 Ts ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  apply reducible_fold_zero; steps;
    eauto with wf;
    eauto 3 with twf;
    eauto with erased.
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
    subset (fv T0) (support gamma) ->
    subset (fv Ts) (support gamma) ->
    [ tvars; gamma ⊨ n : T_nat ] ->
    [ tvars; (p, T_equiv n zero) :: gamma ⊨ t : T0 ] ->
    [ tvars; (p, T_equiv n (succ (fvar pn term_var))) :: (pn, T_nat) :: gamma ⊨
        t : topen 0 Ts (T_rec (fvar pn term_var) T0 Ts) ] ->
    [ tvars; gamma ⊨ t : T_rec n T0 Ts ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  unfold reducible, reduces_to in H23; repeat step || simp_red.

  t_invert_nat_value; steps.

  - apply reducible_rec_equivalent with zero; t_closing;
      eauto using equivalent_sym, equivalent_star.
    apply reducible_fold_zero; steps; eauto with wf twf erased.
    unshelve epose proof (H19 theta ((p, uu) :: lterms) _ _ _);
      repeat step || list_utils || apply SatCons || simp_red || t_substitutions ||
             step_inversion NoDup || rewrite substitute_open in * || apply_any;
      eauto using equivalent_star;
      t_closer;
      eauto with twf.

  - apply reducible_rec_equivalent with (succ v0); steps;
      try solve [ apply equivalent_sym, equivalent_star; t_closing ].

    apply reducible_fold; steps;
      eauto with wf;
      eauto with fv;
      eauto 3 with twf;
      eauto with erased;
      eauto using equivalent_sym, equivalent_star;
      try solve [ unfold reducible, reduces_to; repeat step || simp_red || eexists; try t_closing; eauto with smallstep ].

    unshelve epose proof (H20 theta ((p, uu) :: (pn, v0) :: lterms) _ _ _);
      repeat step || list_utils || nodup || apply SatCons || simp_red || t_substitutions ||
             rewrite substitute_open in *;
      try solve [ apply equivalent_star; t_closing ];
      t_closer;
      eauto with twf.
Qed.

Lemma reducible_unfold_in:
  forall t1 t2 T n T0 Ts theta,
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
    pfv n term_var = nil ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    (forall v,
        reducible_values theta v T0 ->
        equivalent_terms t1 v ->
        equivalent_terms n zero ->
        reducible theta (open 0 t2 v) T) ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ->
        equivalent_terms t1 v ->
        reducible theta (open 0 t2 v) T) ->
    reducible theta (app (notype_lambda t2) t1) T.
Proof.
  intros.
  unfold reducible, reduces_to in H; steps.

  eapply star_backstep_reducible; eauto with cbvlemmas values;
    repeat step || list_utils.

  apply backstep_reducible with (open 0 t2 v); repeat step || list_utils;
      eauto using red_is_val with smallstep;
      eauto with wf;
      eauto with fv;
      eauto with erased.

  simp_red; steps; eauto using equivalent_star.

  apply (
      reducible_rename_one_rc
        _
        (fun t => reducible_values theta t (T_rec (notype_tpred n) T0 Ts))
        _ _ _ X X
   ) in H26;
    eauto with values;
    eauto using reducibility_is_candidate.

  - apply reducible_values_subst_head in H26;
      repeat step || list_utils || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with erased);
    eauto with wf twf fv;
    eauto with erased;
    eauto using equivalent_star.

  - apply equivalent_rc_sym.
    apply equivalent_rc_rec_step; unfold notype_tpred; steps.
    eapply star_trans; eauto with cbvlemmas.
    eapply Trans; eauto with star smallstep values.
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
    subset (pfv n term_var) (support gamma) ->
    subset (pfv T0 term_var) (support gamma) ->
    subset (pfv Ts term_var) (support gamma) ->
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
    [ tvars; gamma ⊨ t1 : T_rec n T0 Ts ] ->
    [ tvars; (p2, T_equiv n zero) :: (p1, T_equiv t1 (fvar y term_var)) :: (y, T0) :: gamma ⊨
        open 0 t2 (fvar y term_var) : T ] ->
    [ tvars; (p1, T_equiv t1 (fvar y term_var)) ::
             (y, topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ::
             gamma ⊨
        open 0 t2 (fvar y term_var) : T ] ->
    [ tvars; gamma ⊨ app (notype_lambda t2) t1 : T ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_reducible_trec.

  eapply reducible_unfold_in; try eassumption;
    steps;
    eauto with wf;
    eauto with twf;
    eauto with fv;
    eauto with erased.

  - unshelve epose proof (H45 theta ((p2, uu) :: (p1, uu) :: (y, v) :: lterms) _ _ _);
      repeat step || list_utils || nodup || apply SatCons || simp_red || t_substitutions;
      t_closer.

  - unshelve epose proof (H46 theta ((p1, uu) :: (y, v) :: lterms) _ _ _);
      repeat match goal with
             | |- reducible_values _ _ T_nat => simp reducible_values
             | |- reducible_values _ _ (T_equiv _ _) => simp reducible_values
             | _ => repeat step || list_utils || nodup || apply SatCons || t_substitutions || fv_open
             end;
      t_closer.
Qed.

Lemma equivalent_zero_contradiction:
  forall n,
    equivalent_terms (tlt zero n) ttrue ->
    star scbv_step n zero ->
    False.
Proof.
  intros.
  apply (equivalent_tlt_terms_trans _ _ zero zero) in H;
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
    pfv n term_var = nil ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    equivalent_terms (tlt zero n) ttrue ->
    (forall v,
        reducible_values theta v (topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ->
        equivalent_terms t1 v ->
        reducible theta (open 0 t2 v) T) ->
    reducible theta (app (notype_lambda t2) t1) T.
Proof.
  intros.
  unfold reducible, reduces_to in H; steps.
  eapply star_backstep_reducible; eauto with cbvlemmas values; repeat step || list_utils;
    eauto with wf.

  apply backstep_reducible with (open 0 t2 v); repeat step || list_utils;
    eauto using red_is_val with smallstep;
    eauto with wf;
    eauto with fv;
    eauto with erased.

  simp_red; steps; eauto using equivalent_zero_contradiction with exfalso.

  apply (
      reducible_rename_one_rc
        _
        (fun t => reducible_values theta t (T_rec (notype_tpred n) T0 Ts))
        _ _ _ X X
   ) in H26;
    eauto with values;
    eauto using reducibility_is_candidate.
  - apply reducible_values_subst_head in H26;
      repeat step || list_utils || t_fv_red || rewrite is_erased_term_tfv in * by (steps; eauto with erased);
    eauto with wf twf fv.

    apply_any; steps; eauto using equivalent_star.

  - apply equivalent_rc_sym.
    apply equivalent_rc_rec_step; unfold notype_tpred; steps.
    eapply star_trans; eauto with cbvlemmas.
    eapply Trans; eauto with star smallstep values.
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
    subset (pfv n term_var) (support gamma) ->
    subset (pfv T0 term_var) (support gamma) ->
    subset (pfv Ts term_var) (support gamma) ->
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
    [ tvars; gamma ⊨ t1 : T_rec n T0 Ts ] ->
    (forall theta l,
      valid_interpretation theta ->
      satisfies (reducible_values theta) gamma l ->
      support theta = tvars ->
      equivalent_terms (substitute (tlt zero n) l) ttrue) ->
    [ tvars;
        (p1, T_equiv t1 (fvar y term_var)) ::
        (y, topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ::
        gamma ⊨
          open 0 t2 (fvar y term_var) : T ] ->
    [ tvars; gamma ⊨ app (notype_lambda t2) t1 : T ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_reducible_trec.

  eapply reducible_unfold_pos_in; try eassumption;
    steps;
    eauto with wf;
    eauto with twf;
    eauto with fv;
    eauto with erased.

  unshelve epose proof (H37 theta ((p1, uu) :: (y, v) :: lterms) _ _ _);
    repeat match goal with
           | |- reducible_values _ _ T_nat => simp reducible_values
           | |- reducible_values _ _ (T_equiv _ _) => simp reducible_values
           | _ => repeat step || list_utils || nodup || apply SatCons || t_substitutions || fv_open
           end;
      t_closer.
Qed.
