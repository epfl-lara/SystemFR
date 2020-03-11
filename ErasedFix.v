Require Import Equations.Equations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.ReducibilityEquivalent.
Require Export SystemFR.NatLessThan.
Require Export SystemFR.ErasedArrow.
Require Export SystemFR.ErasedPair.
Require Export SystemFR.ErasedQuant.
Require Export SystemFR.ErasedNat.

Require Import Omega.

Opaque reducible_values.
Opaque makeFresh.
Opaque tlt.

Lemma reducible_fix_zero:
  forall theta T ts v,
    wf ts 1 ->
    wf T 1 ->
    pfv ts term_var = nil ->
    pfv T term_var = nil ->
    valid_interpretation theta ->
    is_erased_term ts ->
    is_erased_type T ->
    star scbv_step (notype_tfix ts) v ->
    cbv_value v ->
    (forall tx n,
      reducible_values theta n T_nat ->
      reducible_values theta tx
                       (T_forall (T_refine T_nat (tlt (lvar 0 term_var) n)) T) ->
      equivalent_terms tx (notype_tfix ts) ->
      reducible theta (open 0 ts tx) (open 0 T n)) ->
    reducible theta (notype_tfix ts) (open 0 T zero).
Proof.
  intros.
  eapply backstep_reducible; steps;
    eauto with smallstep;
    eauto with wf.

  apply reducibility_equivalent2 with (open 0 (open 1 ts zero) v);
    repeat step || apply equivalent_context || simp_red_goal || simp_red_top_level_hyp ||
           rewrite open_tlt in * || apply_any ||
           rewrite (open_none ts) by (steps; unshelve eauto with wf; auto);
    try solve [ apply equivalent_sym; equivalent_star ];
    eauto 2 with wf fv erased step_tactic;
    eauto using tlt_a_zero with exfalso.

  unfold closed_value, closed_term; steps;
    eauto using wf_star_smallstep with fv wf erased step_tactic.
Qed.

Lemma scbv_step_fix_open:
  forall ts,
    wf ts 1 ->
    scbv_step (notype_tfix ts) (open 0 ts (notype_tfix ts)).
Proof.
  intros.
  eapply scbv_step_same; eauto with smallstep.
  rewrite (open_none ts); steps; eauto with wf.
Qed.

Lemma reducible_fix_strong_induction_aux:
  forall n theta T tsv v ts,
    tree_size v < n ->
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_nat_value v ->
    is_erased_term ts ->
    is_erased_type T ->
    valid_interpretation theta ->
    star scbv_step (notype_tfix ts) tsv ->
    cbv_value tsv ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx
         (T_forall (T_refine T_nat (tlt (lvar 0 term_var) n)) T) ->
       equivalent_terms tx (notype_tfix ts) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T n)) ->
    reducible theta (notype_tfix ts) (open 0 T v).
Proof.
  induction n; repeat step || simp_red_goal || simp_red_top_level_hyp; try omega;
    eapply backstep_reducible;
      repeat step || list_utils;
      eauto using scbv_step_fix_open;
      eauto with wf.

  apply reducibility_equivalent2 with (open 0 (open 1 ts zero) tsv);
    repeat step || apply equivalent_context || apply_any || simp_red_goal || simp_red_top_level_hyp ||
           rewrite open_tlt in * ||
           rewrite (open_none ts) by (steps; unshelve eauto with wf; auto);
    try solve [ apply equivalent_sym; equivalent_star ];
    eauto 2 with wf fv erased step_tactic.

  - unfold closed_value, closed_term; steps;
      eauto using wf_star_smallstep with fv wf erased step_tactic.

  - apply reducible_expr_value; auto.
    apply reducibility_equivalent2 with (notype_tfix ts);
      try solve [ equivalent_star ];
      eauto 2 with wf fv erased step_tactic.

    apply IHn with tsv;
      repeat step || simp_red_goal || simp_red_top_level_hyp || rewrite open_tlt in * || tlt_sound ||
      rewrite open_none in * by t_closer;
      try solve [ unshelve t_closer; auto ];
      try omega.
Qed.

Lemma reducible_fix_strong_induction:
  forall theta T v ts tsv,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_nat_value v ->
    is_erased_term ts ->
    is_erased_type T ->
    valid_interpretation theta ->
    star scbv_step (notype_tfix ts) tsv ->
    cbv_value tsv ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx
         (T_forall (T_refine T_nat (tlt (lvar 0 term_var) n)) T) ->
       equivalent_terms tx (notype_tfix ts) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T n)) ->
    reducible theta (notype_tfix ts) (open 0 T v).
Proof.
  eauto using reducible_fix_strong_induction_aux.
Qed.

Lemma reducible_fix_strong_induction_forall:
  forall theta ts tsv T,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_erased_term ts ->
    valid_interpretation theta ->
    is_erased_type T ->
    star scbv_step (notype_tfix ts) tsv ->
    cbv_value tsv ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx
                        (T_forall (T_refine T_nat (tlt (lvar 0 term_var) n)) T) ->
       equivalent_terms tx (notype_tfix ts) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T n)) ->
    reducible theta (notype_tfix ts) (T_forall T_nat T).
Proof.
  repeat step.

  apply reducible_forall with (open 0 T zero); steps;
    eauto using reducible_fix_zero.

  eapply reducible_fix_strong_induction; repeat step || simp_red_goal || simp_red_top_level_hyp;
   eauto with fv wf.
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
    cbv_value ts ->
    NoDup (n :: y :: p :: nil) ->
    [ tvars;
        (p, T_equiv (fvar y term_var) (notype_tfix ts)) ::
        (y,
          (T_forall
             (T_refine T_nat (tlt (lvar 0 term_var) (fvar n term_var)))
             T)
        ) ::
        (n, T_nat) ::
        gamma ⊨
      open 0 ts (fvar y term_var) : open 0 T (fvar n term_var) ] ->
    [ tvars; gamma ⊨ notype_tfix ts : T_forall T_nat T ].
Proof.
  unfold open_reducible in *; steps.

  apply reducible_fix_strong_induction_forall with
      (open 0 (psubstitute ts lterms term_var) (notype_tfix (psubstitute ts lterms term_var)));
        repeat step || apply star_one || apply scbv_step_fix_open ||
               apply cbv_value_open || apply cbv_value_subst;
    unshelve eauto with wf;
    eauto with fv;
    eauto with erased;
    try solve [ rewrite substitute_open2; eauto with wf ].

  unshelve epose proof (H15 theta ((p, uu) :: (y, tx) :: (n, n0) :: lterms) _ _ _) as HH;
    repeat step || apply SatCons || nodup || rewrite pfv_tlt in * || rewrite pfv_shift2 in * || list_utils;
    eauto 2 with fv;
    eauto 2 with wf;
    eauto 2 with twf.

  - repeat step || t_substitutions || simp_red_goal.
  - repeat step || rewrite psubstitute_tlt in * || (rewrite substitute_shift in * by eauto 2 with wf step_tactic) || t_substitutions.
  - repeat step || t_substitutions || nodup.
Qed.
