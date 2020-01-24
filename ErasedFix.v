Require Import Equations.Equations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ErasedNat.
Require Export SystemFR.ErasedQuant.
Require Export SystemFR.ErasedPair.

Require Import Omega.

Opaque reducible_values.
Opaque makeFresh.
Opaque tlt.

Lemma reducible_fix_zero:
  forall theta T ts,
    wf ts 1 ->
    pfv ts term_var = nil ->
    valid_interpretation theta ->
    is_erased_term ts ->
    is_erased_type T ->
    (forall tx n : tree,
        reducible_values theta n T_nat ->
        reducible_values theta tx
                         (T_forall (T_refine T_nat (tlt (lvar 0 term_var) n))
                                   (T_arrow T_unit (shift 0 T 1))) ->
        equivalent_terms tx (notype_lambda (notype_tfix ts)) ->
        reducible theta (open 0 ts tx) (open 0 T n)) ->
    reducible theta (notype_tfix ts) (open 0 T zero).
Proof.
  intros.
  eapply backstep_reducible; eauto with smallstep;
    repeat
        step || apply_any || simp_red || rewrite open_tlt in * ||
        rewrite (open_none ts) by (steps; unshelve eauto with wf; auto);
      try solve [ unshelve t_closing; auto ];
      eauto using tlt_a_zero with exfalso;
      try solve [ unshelve eauto 4 using equivalent_refl with erased wf fv step_tactic; auto ].
Qed.

Lemma scbv_step_fix_open:
  forall ts : tree,
    wf ts 1 ->
    scbv_step (notype_tfix ts) (open 0 ts (notype_lambda (notype_tfix ts))).
Proof.
  intros.
  eapply scbv_step_same; eauto with smallstep.
  rewrite (open_none ts); steps; eauto with wf.
Qed.

Lemma reducible_fix_strong_induction_aux:
  forall n theta T v ts,
    tree_size v < n ->
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_nat_value v ->
    is_erased_term ts ->
    is_erased_type T ->
    valid_interpretation theta ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx
         (T_forall
            (T_refine T_nat (tlt (lvar 0 term_var) n))
            (T_arrow T_unit (shift 0 T 1))) ->
       equivalent_terms tx (notype_lambda (notype_tfix ts)) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T n)) ->
    reducible theta (notype_tfix ts) (open 0 T v).
Proof.
  induction n; repeat step || simp_red || apply reducible_let; try omega;
    eauto using reducible_fix_zero.
    eapply backstep_reducible;
      repeat step || list_utils || apply_any || simp reducible_values || rewrite reducibility_rewrite;
      eauto using scbv_step_fix_open;
      eauto 3 with smallstep values;
      eauto with fv;
      try solve [ unshelve eauto 2 with wf; auto ];
      eauto with erased;
      eauto using reducible_nat_value;
      try solve [ unshelve t_closing; auto ];
      try solve [ apply equivalent_refl; steps; eauto with wf ].

  eapply backstep_reducible; eauto using red_is_val with smallstep;
    repeat
      step || list_utils || rewrite <- open_shift_zero in * ||
      rewrite open_none by (steps; eauto with wf) ||
      rewrite (open_none ts) in * by (steps; eauto with wf);
      try solve [ unshelve eauto with wf fv; auto ].

  apply_any;
    repeat step || simp_red || rewrite open_tlt in * || t_tlt_sound ||
    rewrite open_none in * by t_closer;
    try solve [ unshelve t_closer; auto ];
    try omega.
Qed.

Lemma reducible_fix_strong_induction:
  forall theta T v ts,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_nat_value v ->
    is_erased_term ts ->
    is_erased_type T ->
    valid_interpretation theta ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx
         (T_forall
            (T_refine T_nat (tlt (lvar 0 term_var) n))
            (T_arrow T_unit (shift 0 T 1))) ->
       equivalent_terms tx (notype_lambda (notype_tfix ts)) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T n)) ->
    reducible theta (notype_tfix ts) (open 0 T v).
Proof.
  eauto using reducible_fix_strong_induction_aux.
Qed.

Lemma reducible_fix_strong_induction_forall:
  forall theta ts T,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_erased_term ts ->
    valid_interpretation theta ->
    is_erased_type T ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx
                        (T_forall
                           (T_refine T_nat (tlt (lvar 0 term_var) n))
                           (T_arrow T_unit (shift 0 T 1))) ->
       equivalent_terms tx (notype_lambda (notype_tfix ts)) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T n)) ->
    reducible theta (notype_tfix ts) (T_forall T_nat T).
Proof.
  repeat step.

  apply reducible_forall with (open 0 T zero); steps;
    eauto using reducible_fix_zero.

  apply reducible_fix_strong_induction; repeat step || simp_red;
     repeat step; eauto with fv wf b_equiv.
Qed.

Lemma open_reducible_fix_strong_induction:
  forall tvars ts gamma T n y p,
    wf T 1 ->
    wf ts 1 ->
    subset (fv T) (support gamma) ->
    subset (fv ts) (support gamma) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context gamma) ->
    ~(y ∈ fv ts) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    is_erased_term ts ->
    is_erased_type T ->
    NoDup (n :: y :: p :: nil) ->
    [ tvars;
        (p, T_equiv (fvar y term_var) (notype_lambda (notype_tfix ts))) ::
        (y,
          (T_forall
             (T_refine T_nat (tlt (lvar 0 term_var) (fvar n term_var)))
             (T_arrow T_unit (shift 0 T 1)))) ::
        (n, T_nat) ::
        gamma ⊨
      open 0 ts (fvar y term_var) : open 0 T (fvar n term_var) ] ->
    [ tvars; gamma ⊨ notype_tfix ts : T_forall T_nat T ].
Proof.
  unfold open_reducible in *; steps.

  apply reducible_fix_strong_induction_forall; repeat step;
    unshelve eauto with wf;
    eauto with fv;
    eauto with erased;
    try solve [ rewrite substitute_open2; eauto with wf ].

  unshelve epose proof (H14 theta ((p, uu) :: (y,tx) :: (n,n0) :: lterms) _ _ _) as HH;
    repeat step || apply SatCons || nodup || rewrite pfv_tlt in * || rewrite pfv_shift2 in * || list_utils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto 2 with twf.

  - repeat step || simp_red || t_substitutions.
  - repeat step || rewrite psubstitute_tlt in * || (rewrite substitute_shift in * by eauto 2 with wf step_tactic) || t_substitutions.
  - repeat step || t_substitutions || nodup.
Qed.

Lemma reducible_fix_induction:
  forall v, is_nat_value v -> forall theta T ts,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_erased_term ts ->
    is_erased_type T ->
    valid_interpretation theta ->
    (forall tx, reducible_values theta tx T_top -> reducible theta (open 0 ts tx) (open 0 T zero)) ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
       equivalent_terms tx (notype_lambda (notype_tfix ts)) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T (succ n))) ->
    reducible theta (notype_tfix ts) (open 0 T v).
Proof.
  induction 1; repeat step || simp_red.

  - (* zero *)
    eapply backstep_reducible; eauto using scbv_step_fix_open;
      repeat step || list_utils || apply_any || simp_red;
      t_closer.
  - (* succ v *)
    eapply backstep_reducible; eauto using scbv_step_fix_open;
      repeat step || list_utils || apply_any;
      eauto 3 with smallstep values;
      eauto with fv;
      eauto 2 with wf;
      eauto with erased;
      eauto using reducible_nat_value;
      try solve [ apply equivalent_refl; steps; eauto with wf ].

    apply reducible_lambda;
      repeat apply reducible_let with T_unit || simp reducible_values ||
             apply reducible_intersection || step || list_utils || t_substitutions ||
             (rewrite open_none by t_rewrite);
      eauto with erased wf.
Qed.

Lemma reducible_fix_induction_forall:
  forall theta ts T,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_erased_term ts ->
    is_erased_type T ->
    valid_interpretation theta ->
    (forall tx,
        reducible_values theta tx T_top ->
        reducible theta (open 0 ts tx) (open 0 T zero)) ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
       equivalent_terms tx (notype_lambda (notype_tfix ts)) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T (succ n))) ->
    reducible theta (notype_tfix ts) (T_forall T_nat T).
Proof.
  repeat step.
  pose proof H6 as HH.
  unfold reducible, reduces_to in HH; steps.

  apply reducible_forall with (open 0 T zero); steps.

  - eapply backstep_reducible; eauto using scbv_step_fix_open;
      repeat step || apply_any || simp reducible_values;
      eauto with smallstep; try t_closing.

  - apply reducible_fix_induction; repeat step || simp_red;
     repeat step; eauto with fv wf b_equiv.
Qed.

Lemma open_reducible_fix:
  forall tvars ts gamma T n y p,
    wf T 1 ->
    wf ts 1 ->
    subset (fv T) (support gamma) ->
    subset (fv ts) (support gamma) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context gamma) ->
    ~(y ∈ fv ts) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    is_erased_term ts ->
    is_erased_type T ->
    NoDup (n :: y :: p :: nil) ->
    [ tvars; (y, T_top) :: gamma ⊨ open 0 ts (fvar y term_var) : open 0 T zero ] ->
    [ tvars;
        (p, T_equiv (fvar y term_var) (notype_lambda (notype_tfix ts))) ::
        (y, T_arrow T_unit (open 0 T (fvar n term_var))) ::
        (n, T_nat) ::
        gamma ⊨
          open 0 ts (fvar y term_var) : open 0 T (succ (fvar n term_var)) ] ->
    [ tvars; gamma ⊨ notype_tfix ts : T_forall T_nat T ].
Proof.
  unfold open_reducible in *; steps.

  apply reducible_fix_induction_forall; repeat step;
    unshelve eauto with wf;
    eauto with fv;
    eauto with erased;
    try solve [ rewrite substitute_open2; eauto with wf ].

  - unshelve epose proof (H14 theta ((y, tx) :: lterms) _ _ _);
      repeat step || list_utils || t_substitutions || simp_red || apply SatCons ||
             step_inversion NoDup || rewrite substitute_open in * || apply_any;
        t_closer.

  - unshelve epose proof (H15 theta ((p, uu) :: (y,tx) :: (n,n0) :: lterms) _ _ _);
      repeat step || apply SatCons || nodup || list_utils || fv_open;
        eauto 2 with fv;
        eauto 2 with wf;
        eauto 2 with twf.

    + repeat step || simp_red || t_substitutions.
    + repeat step || rewrite psubstitute_tlt in * || (rewrite substitute_shift in * by eauto 2 with wf step_tactic) || t_substitutions.
    + repeat step || t_substitutions || nodup.
Qed.
