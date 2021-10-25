From Equations Require Import Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilitySubst.
Require Export SystemFR.SomeTerms.
Require Export SystemFR.ErasedPrimitive.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_values_rec_step:
  forall ρ t1 t2 T0 Ts v,
    [ ρ ⊨ v : T_rec t1 T0 Ts ]v ->
    t1 ~>* t2 ->
    [ ρ ⊨ v : T_rec t2 T0 Ts ]v.
Proof.
  repeat step || simp_red;
    eauto with erased.
  - left; steps; eapply star_many_steps; eauto; unfold irred; repeat step || t_invert_step.
  - right. unshelve eexists n', X, _, _; steps;
             eauto using is_nat_value_value, value_irred, star_many_steps with values.
Qed.

Lemma reducible_values_rec_backstep:
  forall ρ t1 t2 T0 Ts v,
    [ ρ ⊨ v : T_rec t1 T0 Ts ]v ->
    is_erased_term t2 ->
    t2 ~>* t1 ->
    [ ρ ⊨ v : T_rec t2 T0 Ts ]v.
Proof.
  repeat step || simp_red;
    eauto with erased.
  - left; steps; eauto using star_trans.
  - right. unshelve eexists n', X, _, _; steps; eauto using star_trans.
Qed.

Lemma reducible_values_rec_equivalent:
  forall ρ t1 t2 T0 Ts v,
    [ ρ ⊨ v : T_rec t1 T0 Ts ]v ->
    [ t1 ≡ t2 ] ->
    [ ρ ⊨ v : T_rec t2 T0 Ts ]v.
Proof.
  repeat step || simp_red;
    eauto with erased;
    try solve [ unfold equivalent_terms in *; steps ].
  - left; steps; eauto using equivalent_star_nat, INVZero.
  - right; unshelve eexists n', X, _, _; steps; eauto using equivalent_star_nat, INVSucc.
Qed.

Lemma reducible_rec_equivalent:
  forall ρ t1 t2 T0 Ts t,
    [ ρ ⊨ t : T_rec t1 T0 Ts ] ->
    valid_interpretation ρ ->
    [ t1 ≡ t2 ] ->
    [ ρ ⊨ t : T_rec t2 T0 Ts ].
Proof.
  eauto using reducible_values_rec_equivalent, reducible_values_exprs.
Qed.

Lemma equivalent_rc_rec_step:
  forall ρ t1 t2 T0 Ts,
    is_erased_term t1 ->
    t1 ~>* t2 ->
    equivalent_rc
      (fun t => [ ρ ⊨ t : T_rec t1 T0 Ts ]v)
      (fun t => [ ρ ⊨ t : T_rec t2 T0 Ts ]v).
Proof.
  unfold equivalent_rc; steps;
    eauto using reducible_values_rec_step, reducible_values_rec_backstep.
Qed.

Lemma reducible_values_unfold:
  forall ρ v n T0 Ts,
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
    valid_interpretation ρ ->
    [ ρ ⊨ v : T_rec (succ n) T0 Ts ]v ->
    [ ρ ⊨ v : topen 0 Ts (T_rec n T0 Ts) ]v.
Proof.
  unfold reduces_to;
    repeat match goal with
           | H: succ _ ~>* ?v |- _ =>
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
  forall ρ, [ ρ ⊨ succ zero : T_nat ]v.
Proof.
  repeat step || simp_red.
Qed.

Ltac inst_one :=
  match goal with
  | H: forall a, [ ?ρ ⊨ _ : T_nat ]v -> _ |- _ =>
      poseNew (Mark 0 "once"); unshelve epose proof (H (succ zero) (red_one ρ))
  end.

Lemma reducible_unfold:
  forall ρ t n T0 Ts,
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
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_rec (succ n) T0 Ts ] ->
    [ ρ ⊨ t : topen 0 Ts (T_rec n T0 Ts) ].
Proof.
  unfold reduces_to;
    repeat match goal with
           | _ => find_smallstep_value
           | _ => apply reducible_values_unfold
           | _ => step || unfold closed_value in *
           end; eauto with values.
Qed.

Lemma open_reducible_unfold:
  forall Θ Γ t n T0 Ts,
    wf n 0 ->
    twf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (fv n) (support Γ) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    [ Θ; Γ ⊨ t : T_rec (succ n) T0 Ts ] ->
    [ Θ; Γ ⊨ t : topen 0 Ts (T_rec n T0 Ts) ].
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
    n ~>* v ->
    [ spositive n ≡ ttrue ] ->
    [ n ≡ succ (tmatch n notype_err (lvar 0 term_var)) ].
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
    eapply Relation_Operators.rt1n_trans; eauto with smallstep; steps.

  - apply equivalent_sym.
    apply equivalent_star; steps;
      try solve [ top_level_unfold equivalent_terms; repeat step || list_utils ].
Qed.

Lemma reducible_trec:
  forall ρ v n T0 Ts,
   [ ρ ⊨ v : T_rec n T0 Ts ] ->
    exists v', is_nat_value v' /\ n ~>* v'.
Proof.
  unfold reduces_to; repeat step || simp_red.
  - exists zero; steps.
  - exists (succ n'); steps; eauto with is_nat_value.
Qed.

Ltac t_reducible_trec :=
  match goal with
  | H:[ _ ⊨ _ : T_rec _ _ _ ] |- _ =>
    poseNew (Mark H "reducible_trec");
    pose proof (reducible_trec _ _ _ _ _ H)
  end.

Lemma open_reducible_unfold2:
  forall Θ Γ t n T0 Ts,
    wf n 0 ->
    twf n 0 ->
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    subset (fv n) (support Γ) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    (forall ρ l,
       valid_interpretation ρ ->
       satisfies (reducible_values ρ) Γ l ->
       support ρ = Θ ->
       [ spositive (psubstitute n l term_var) ≡ ttrue ]) ->
    [ Θ; Γ ⊨ t : T_rec n T0 Ts ] ->
    [ Θ; Γ ⊨ t : topen 0 Ts (T_rec (notype_tpred n) T0 Ts) ].
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
  forall ρ t n T0 Ts,
    valid_interpretation ρ ->
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    [ ρ ⊨ n : T_nat ]  ->
    [ ρ ⊨ t : topen 0 Ts (T_rec n T0 Ts) ] ->
    [ ρ ⊨ t : T_rec (succ n) T0 Ts ].
Proof.
  unfold reduces_to;
    repeat match goal with
           | _ => step || simp_red
           end; eauto with values.

  eexists; steps; eauto with cbvlemmas; t_closer.

  right.
  unshelve eexists v0, (makeFresh (pfv n type_var :: pfv v0 type_var :: pfv T0 type_var :: pfv Ts type_var :: support ρ :: nil)), _, _;
    repeat step;
    try finisher;
    eauto with cbvlemmas.

  match goal with
  | |- [ (?M,_) :: _ ⊨ _ : _ ]v =>
    eapply (reducible_rename_one_rc (fun v => [ ρ ⊨ v : T_rec n T0 Ts ]v) _ _ _ _ M M);
    repeat step || apply equivalent_rc_rec_step
  end;
    try finisher; t_closer;
    eauto using reducibility_is_candidate.

  apply reducible_values_subst_head2; repeat step || list_utils;
    try finisher;
    t_closer.
Qed.

Lemma open_reducible_fold:
  forall Θ Γ t n T0 Ts,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    [ Θ; Γ ⊨ n : T_nat ] ->
    [ Θ; Γ ⊨ t : topen 0 Ts (T_rec n T0 Ts) ] ->
    [ Θ; Γ ⊨ t : T_rec (succ n) T0 Ts ].
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
  forall ρ t T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    valid_interpretation ρ ->
    [ ρ ⊨ t : T_rec zero T0 Ts ] ->
    [ ρ ⊨ t : T0 ].
Proof.
  unfold reduces_to;
    repeat match goal with
           | _ => apply reducible_values_unfold
           | _ => step || unfold closed_value in * || simp_red || t_invert_star
           end; eauto with values.
Qed.

Lemma open_reducible_unfold_zero:
  forall Θ Γ t T0 Ts,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    [ Θ; Γ ⊨ t : T_rec zero T0 Ts ] ->
    [ Θ; Γ ⊨ t : T0 ].
Proof.
  unfold open_reducible;
    repeat step || rewrite substitute_topen;
      eauto with twf.

  eapply reducible_unfold_zero; steps;
    eauto with wf twf erased.
Qed.

Lemma open_reducible_unfold_zero2:
  forall Θ Γ t T0 Ts n,
    wf T0 0 ->
    wf Ts 0 ->
    twf T0 0 ->
    twf Ts 1 ->
    is_erased_term n ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    (forall ρ l,
       valid_interpretation ρ ->
       satisfies (reducible_values ρ) Γ l ->
       support ρ = Θ ->
       [ substitute n l ≡ zero ]) ->
    [ Θ; Γ ⊨ t : T_rec n T0 Ts ] ->
    [ Θ; Γ ⊨ t : T0 ].
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
  forall ρ t T0 Ts,
    valid_interpretation ρ ->
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    [ ρ ⊨ t : T0 ]  ->
   [ ρ ⊨ t : T_rec zero T0 Ts ].
Proof.
  unfold reduces_to;
    repeat match goal with
           | _ => step || simp_red
           end; eauto with values.

  eexists; steps; eauto with cbvlemmas; t_closer.
  repeat step || simp_red; t_closer; eauto with star.
Qed.

Lemma open_reducible_fold_zero:
  forall Θ Γ t T0 Ts,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    [ Θ; Γ ⊨ t : T0 ] ->
    [ Θ; Γ ⊨ t : T_rec zero T0 Ts ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  apply reducible_fold_zero; steps;
    eauto with wf;
    eauto 3 with twf;
    eauto with erased.
Qed.

Lemma open_reducible_fold2:
  forall Θ Γ t n T0 Ts p pn,
    wf T0 0 ->
    twf T0 0 ->
    wf Ts 0 ->
    twf Ts 1 ->
    is_erased_type T0 ->
    is_erased_type Ts ->
    ~(p ∈ pfv n term_var) ->
    ~(p ∈ pfv_context Γ term_var) ->
    ~(p ∈ pfv t term_var) ->
    ~(p ∈ pfv T0 term_var) ->
    ~(p ∈ pfv Ts term_var) ->
    ~(pn ∈ pfv n term_var) ->
    ~(pn ∈ pfv_context Γ term_var) ->
    ~(pn ∈ pfv t term_var) ->
    ~(pn ∈ pfv T0 term_var) ->
    ~(pn ∈ pfv Ts term_var) ->
    ~(p = pn) ->
    subset (fv T0) (support Γ) ->
    subset (fv Ts) (support Γ) ->
    [ Θ; Γ ⊨ n : T_nat ] ->
    [ Θ; (p, T_equiv n zero) :: Γ ⊨ t : T0 ] ->
    [ Θ; (p, T_equiv n (succ (fvar pn term_var))) :: (pn, T_nat) :: Γ ⊨
        t : topen 0 Ts (T_rec (fvar pn term_var) T0 Ts) ] ->
    [ Θ; Γ ⊨ t : T_rec n T0 Ts ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3.

  unfold reduces_to in H23; repeat step || simp_red.

  t_invert_nat_value; steps.

  - apply reducible_rec_equivalent with zero; t_closing;
      eauto using equivalent_sym, equivalent_star.
    apply reducible_fold_zero; steps; eauto with wf twf erased.
    unshelve epose proof (H19 ρ ((p, uu) :: lterms) _ _ _);
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
      try solve [ unfold reduces_to; repeat step || simp_red || eexists; try t_closing; eauto with smallstep ].

    unshelve epose proof (H20 ρ ((p, uu) :: (pn, v0) :: lterms) _ _ _);
      repeat step || list_utils || nodup || apply SatCons || simp_red || t_substitutions ||
             rewrite substitute_open in *;
      try solve [ apply equivalent_star; t_closing ];
      t_closer;
      eauto with twf.
Qed.

Lemma reducible_unfold_in:
  forall t1 t2 T n T0 Ts ρ,
   [ ρ ⊨ t1 : T_rec n T0 Ts ] ->
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
    valid_interpretation ρ ->
    pfv n term_var = nil ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    (forall v,
        [ ρ ⊨ v : T0 ]v ->
        [ t1 ≡ v ] ->
        [ n ≡ zero ] ->
        [ ρ ⊨ open 0 t2 v : T ]) ->
    (forall v,
        [ ρ ⊨ v : topen 0 Ts (T_rec (notype_tpred n) T0 Ts) ]v ->
        [ t1 ≡ v ] ->
        [ ρ ⊨ open 0 t2 v : T ]) ->
    [ ρ ⊨ app (notype_lambda t2) t1 : T ].
Proof.
  intros.
  unfold reduces_to in H; steps.

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
        (fun t => [ ρ ⊨ t : T_rec (notype_tpred n) T0 Ts ]v)
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
    eapply Relation_Operators.rt1n_trans; eauto with star smallstep values.
Qed.

Lemma open_reducible_unfold_in:
  forall Θ Γ t1 t2 T n T0 Ts p1 p2 y,
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
    subset (pfv t1 term_var) (support Γ) ->
    subset (pfv t2 term_var) (support Γ) ->
    subset (pfv n term_var) (support Γ) ->
    subset (pfv T0 term_var) (support Γ) ->
    subset (pfv Ts term_var) (support Γ) ->
    ~(p1 ∈ Θ) ->
    ~(p1 ∈ pfv_context Γ term_var) ->
    ~(p1 ∈ support Γ) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(p2 ∈ Θ) ->
    ~(p2 ∈ pfv_context Γ term_var) ->
    ~(p2 ∈ support Γ) ->
    ~(p2 ∈ fv t1) ->
    ~(p2 ∈ fv t2) ->
    ~(p2 ∈ fv n) ->
    ~(p2 ∈ fv T0) ->
    ~(p2 ∈ fv Ts) ->
    ~(p2 ∈ fv T) ->
    ~(y ∈ Θ) ->
    ~(y ∈ pfv_context Γ term_var) ->
    ~(y ∈ support Γ) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    NoDup (p1 :: p2 :: y :: nil) ->
    [ Θ; Γ ⊨ t1 : T_rec n T0 Ts ] ->
    [ Θ; (p2, T_equiv n zero) :: (p1, T_equiv t1 (fvar y term_var)) :: (y, T0) :: Γ ⊨
        open 0 t2 (fvar y term_var) : T ] ->
    [ Θ; (p1, T_equiv t1 (fvar y term_var)) ::
             (y, topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ::
             Γ ⊨
        open 0 t2 (fvar y term_var) : T ] ->
    [ Θ; Γ ⊨ app (notype_lambda t2) t1 : T ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_reducible_trec.

  eapply reducible_unfold_in; try eassumption;
    steps;
    eauto with wf;
    eauto with twf;
    eauto with fv;
    eauto with erased.

  - unshelve epose proof (H45 ρ ((p2, uu) :: (p1, uu) :: (y, v) :: lterms) _ _ _);
      repeat step || list_utils || nodup || apply SatCons || simp_red || t_substitutions;
      t_closer.

  - unshelve epose proof (H46 ρ ((p1, uu) :: (y, v) :: lterms) _ _ _);
      repeat match goal with
             | |- [ _ ⊨ _ : T_nat ]v => simp reducible_values
             | |- [ _ ⊨ _ : T_equiv _ _ ]v => simp reducible_values
             | _ => repeat step || list_utils || nodup || apply SatCons || t_substitutions || fv_open
             end;
      t_closer.
Qed.


Lemma equivalent_zero_contradiction:
  forall n,
    [ binary_primitive Lt zero n ≡ ttrue ] ->
    n ~>* zero ->
    False.
Proof.
  intros.
  apply_anywhere equivalent_true.
  repeat steps || t_deterministic_star || t_invert_star; eauto with values.
Qed.

Lemma reducible_unfold_pos_in:
  forall (t1 t2 T n T0 Ts : tree) (ρ : interpretation),
   [ ρ ⊨ t1 : T_rec n T0 Ts ] ->
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
    valid_interpretation ρ ->
    pfv t1 term_var = nil ->
    pfv t2 term_var = nil ->
    pfv n term_var = nil ->
    pfv T0 term_var = nil ->
    pfv Ts term_var = nil ->
    [ binary_primitive Lt zero n ≡ ttrue ] ->
    (forall v,
        [ ρ ⊨ v : topen 0 Ts (T_rec (notype_tpred n) T0 Ts) ]v ->
        [ t1 ≡ v ] ->
        [ ρ ⊨ open 0 t2 v : T ]) ->
    [ ρ ⊨ app (notype_lambda t2) t1 : T ].
Proof.
  intros.
  unfold reduces_to in H; steps.
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
        (fun t => [ ρ ⊨ t : T_rec (notype_tpred n) T0 Ts ]v)
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
    eapply Relation_Operators.rt1n_trans; eauto with star smallstep values.
Qed.

Lemma open_reducible_unfold_pos_in:
  forall Θ Γ t1 t2 T n T0 Ts p1 y,
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
    subset (pfv t1 term_var) (support Γ) ->
    subset (pfv t2 term_var) (support Γ) ->
    subset (pfv n term_var) (support Γ) ->
    subset (pfv T0 term_var) (support Γ) ->
    subset (pfv Ts term_var) (support Γ) ->
    ~(p1 ∈ Θ) ->
    ~(p1 ∈ pfv_context Γ term_var) ->
    ~(p1 ∈ support Γ) ->
    ~(p1 ∈ fv t1) ->
    ~(p1 ∈ fv t2) ->
    ~(p1 ∈ fv n) ->
    ~(p1 ∈ fv T0) ->
    ~(p1 ∈ fv Ts) ->
    ~(p1 ∈ fv T) ->
    ~(y ∈ Θ) ->
    ~(y ∈ pfv_context Γ term_var) ->
    ~(y ∈ support Γ) ->
    ~(y ∈ fv t1) ->
    ~(y ∈ fv t2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv T0) ->
    ~(y ∈ fv Ts) ->
    ~(y ∈ fv T) ->
    NoDup (p1 :: y :: nil) ->
    [ Θ; Γ ⊨ t1 : T_rec n T0 Ts ] ->
    (forall ρ l,
      valid_interpretation ρ ->
      satisfies (reducible_values ρ) Γ l ->
      support ρ = Θ ->
      [ substitute (binary_primitive Lt zero n) l ≡ ttrue ]) ->
    [ Θ;
        (p1, T_equiv t1 (fvar y term_var)) ::
        (y, topen 0 Ts (T_rec (notype_tpred n) T0 Ts)) ::
        Γ ⊨
          open 0 t2 (fvar y term_var) : T ] ->
    [ Θ; Γ ⊨ app (notype_lambda t2) t1 : T ].
Proof.
  unfold open_reducible;
    repeat step || t_instantiate_sat3 || t_reducible_trec.

  eapply reducible_unfold_pos_in; try eassumption;
    steps;
    eauto with wf;
    eauto with twf;
    eauto with fv;
    eauto with erased.

  unshelve epose proof (H37 ρ ((p1, uu) :: (y, v) :: lterms) _ _ _);
    repeat match goal with
           | |- [ _ ⊨ _ : T_nat ]v => simp reducible_values
           | |- [ _ ⊨ _ : T_equiv _ _ ]v => simp reducible_values
           | _ => repeat step || list_utils || nodup || apply SatCons || t_substitutions || fv_open
           end;
      t_closer.
Qed.
