Require Import Equations.Equations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.ErasedArrow.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_value_zero:
  forall theta, reducible_values theta zero T_nat.
Proof.
  repeat step || simp_red.
Qed.

Lemma reducible_zero:
  forall theta, reducible theta zero T_nat.
Proof.
  repeat step || simp_red || unfold reducible, reduces_to || eexists || constructor.
Qed.

Lemma open_reducible_zero:
  forall tvars gamma,
    [ tvars; gamma ⊨ zero : T_nat ].
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_zero.
Qed.

Lemma reducible_values_succ:
  forall theta v,
    reducible_values theta v T_nat ->
    reducible_values theta (succ v) T_nat.
Proof.
  repeat step || simp_red; eauto with is_nat_value.
Qed.

Lemma reducible_succ:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_nat ->
    reducible theta (succ t) T_nat.
Proof.
  unfold reducible, reduces_to; steps.
  exists (succ v); repeat step || simp_red; eauto with cbvlemmas;
    eauto with is_nat_value.
Qed.

Lemma reducible_nat_value:
  forall theta v,
    is_nat_value v ->
    valid_interpretation theta ->
    reducible_values theta v T_nat.
Proof.
  induction 1; repeat step;
    eauto using reducible_value_zero;
    eauto using reducible_values_succ.
Qed.

Lemma reducible_nat:
  forall theta v,
    is_nat_value v ->
    valid_interpretation theta ->
    reducible theta v T_nat.
Proof.
  induction 1; repeat step;
    eauto using reducible_zero;
    eauto using reducible_succ.
Qed.

Lemma open_reducible_succ:
  forall tvars gamma t,
    [ tvars; gamma ⊨ t : T_nat ] ->
    [ tvars; gamma ⊨ succ t : T_nat ].
Proof.
  unfold open_reducible in *; steps;
    eauto using reducible_succ.
Qed.

Lemma reducible_match:
  forall theta tn t0 ts T,
    fv ts = nil ->
    fv t0 = nil ->
    wf t0 0 ->
    wf ts 1 ->
    is_erased_term t0 ->
    is_erased_term ts ->
    valid_interpretation theta ->
    reducible theta tn T_nat ->
    (equivalent_terms tn zero -> reducible theta t0 T) ->
     (forall n,
        equivalent_terms tn (succ n) ->
        reducible_values theta n T_nat ->
        reducible
          theta
          (open 0 ts n)
          T) ->
    reducible theta (tmatch tn t0 ts) T.
Proof.
  steps.
  unfold reducible, reduces_to in H6; steps.
  eapply star_backstep_reducible with (tmatch v t0 ts);
    repeat step || list_utils || simp_red; t_closer;
      eauto with cbvlemmas.

  t_invert_nat_value; steps.

  - (* zero *)
    eapply backstep_reducible; eauto with smallstep;
      repeat step || list_utils || apply_any; eauto with fv;
      try solve [ eapply equivalent_star; steps; t_closer ].

  - (* succ v *)
    apply backstep_reducible with (open 0 ts v0);
      repeat step || list_utils || apply reducible_nat_value ||
      match goal with
      | H: forall n, _ -> _ -> reducible _ _ _ |-  _ => apply H
      end;
      eauto 4 with smallstep values;
      auto 2 with fv;
      eauto 2 with wf;
      eauto with erased;
      try solve [ eapply equivalent_star; steps; t_closer ].
Qed.

Lemma open_reducible_match:
  forall tvars tn t0 ts gamma T n p,
    wf ts 1 ->
    wf t0 0 ->
    subset (fv ts) (support gamma) ->
    subset (fv t0) (support gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context gamma) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    ~(p = n) ->
    is_erased_term t0 ->
    is_erased_term ts ->
    [ tvars; gamma ⊨ tn : T_nat ] ->
    [ tvars; (p, T_equiv tn zero) :: gamma ⊨ t0 : T ] ->
    [ tvars;
        (p, T_equiv tn (succ (fvar n term_var))) ::
        (n, T_nat) ::
        gamma ⊨
          open 0 ts (fvar n term_var) : T ] ->
    [ tvars; gamma ⊨ tmatch tn t0 ts : T ].
Proof.
  unfold open_reducible in *; repeat step || t_instantiate_sat3.

  apply reducible_match; repeat step || t_termlist;
    eauto with wf;
    eauto using subset_same with fv;
    eauto with erased.

  - (* zero *)
    unshelve epose proof (H14 theta ((p, uu) :: lterms) _ _ _);
      repeat step || apply SatCons || simp_red || t_substitutions;
      t_closer.

  - (* successor *)
    unshelve epose proof (H15 theta ((p, uu) :: (n,n0) :: lterms) _ _ _);
      repeat step || apply SatCons || simp_red || t_substitutions;
      t_closer;
      eauto with twf.
Qed.

Lemma reducible_rec_induction:
  forall v,
    is_nat_value v ->
    forall theta T t0 ts,
       fv T = nil ->
       fv ts = nil ->
       wf T 1 ->
       wf ts 2 ->
       is_erased_term ts ->
       valid_interpretation theta ->
       reducible theta t0 (open 0 T zero) ->
       is_erased_type T ->
        (forall n tx,
           reducible_values theta n T_nat ->
           reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
           equivalent_terms tx (notype_lambda (notype_rec n t0 ts)) ->
           reducible theta
             (open 0 (open 1 ts n) tx)
             (open 0 T (succ n))) ->
       reducible theta (notype_rec v t0 ts) (open 0 T v).
Proof.
  induction 1; repeat step || simp_red || apply reducible_let with T_nat; eauto 2 with is_nat_value.

  - (* zero *)
    eapply backstep_reducible; eauto with smallstep;
      repeat step || list_utils;
      eauto with wf;
      eauto with erased;
      eauto with fv.
  - (* succ v *)
    eapply backstep_reducible; repeat step || list_utils;
      eauto 3 with smallstep values;
      eauto with fv;
      eauto 2 with wf;
      eauto with erased.

    apply_any;
      repeat step || unfold scbv_normalizing in * || list_utils;
      eauto 2 with fv;
      eauto 4 with wf;
      eauto with values smallstep;
      eauto using reducible_nat_value.

    + apply reducible_lambda;
        repeat simp_red || apply reducible_intersection || step || list_utils ||
               (rewrite open_none by t_rewrite);
        eauto with erased wf fv.

    + apply equivalent_refl; repeat step || list_utils;
        eauto with erased fv wf.
Qed.

Lemma reducible_rec:
  forall theta tn t0 ts T,
    fv T = nil ->
    fv ts = nil ->
    fv t0 = nil ->
    wf T 1 ->
    wf ts 2 ->
    is_erased_term ts ->
    valid_interpretation theta ->
    reducible theta tn T_nat ->
    reducible theta t0 (open 0 T zero) ->
    is_erased_type T ->
    (forall tx n,
      reducible_values theta n T_nat ->
      reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
      equivalent_terms tx (notype_lambda (notype_rec n t0 ts)) ->
      reducible theta
        (open 0 (open 1 ts n) tx)
        (open 0 T (succ n))) ->
    reducible theta (notype_rec tn t0 ts) (open 0 T tn).
Proof.
  repeat step.
  unfold reducible, reduces_to in H6; steps.
  eapply star_backstep_reducible with (notype_rec _ t0 ts);
    repeat step || list_utils ||
      unshelve eauto with cbvlemmas ||
      t_closer.

  eapply reducibility_rtl; eauto; t_closer.
  apply reducible_rec_induction; repeat step || simp_red;
    repeat step; eauto with fv wf b_equiv.
Qed.

Lemma open_reducible_rec:
  forall tvars tn t0 ts gamma T n y p,
    wf T 1 ->
    wf ts 2 ->
    subset (fv T) (support gamma) ->
    subset (fv ts) (support gamma) ->
    subset (fv t0) (support gamma) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context gamma) ->
    ~(y ∈ fv t0) ->
    ~(y ∈ fv ts) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv_context gamma) ->
    ~(n ∈ fv t0) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    is_erased_term ts ->
    NoDup (n :: y :: p :: nil) ->
    is_erased_type T ->
    [ tvars; gamma ⊨ tn : T_nat ] ->
    [ tvars; gamma ⊨ t0 : open 0 T zero ] ->
    [ tvars;
        (p, T_equiv (fvar y term_var) (notype_lambda (notype_rec (fvar n term_var) t0 ts))) ::
        (y, T_arrow T_unit (open 0 T (fvar n term_var))) ::
        (n, T_nat) ::
        gamma ⊨
          open 0 (open 1 ts (fvar n term_var)) (fvar y term_var) :
          open 0 T (succ (fvar n term_var)) ] ->
    [ tvars; gamma ⊨ notype_rec tn t0 ts : open 0 T tn ].
Proof.
  unfold open_reducible in *; repeat step || t_substitutions.

  apply reducible_rec; repeat step;
    unshelve eauto with wf;
    eauto with fv;
    eauto with erased;
    try solve [ rewrite substitute_open2; eauto with wf ].

  unshelve epose proof (H22 theta ((p, uu) :: (y, tx) :: (n, n0) :: lterms) _ _ _);
      repeat step || list_utils || fv_open || t_substitutions || apply SatCons || simp_red ||
             step_inversion NoDup || rewrite substitute_open in *;
      t_closer;
      eauto with twf.
Qed.
