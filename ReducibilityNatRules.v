Require Import Equations.Equations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityArrowRules.
Require Import Termination.RedTactics.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.SmallStep.
Require Import Termination.ListUtils.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TermList.
Require Import Termination.StarRelation.
Require Import Termination.StarInversions.
Require Import Termination.TermForm.
Require Import Termination.SetLemmas.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

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
  repeat step || simp_red || unfold reducible, reduces_to || eexists;
    eauto with smallstep step_tactic.
Qed.

Lemma open_reducible_zero:
  forall theta gamma,
    open_reducible theta gamma zero T_nat.
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_zero.
Qed.

Lemma reducible_values_succ:
  forall theta v,
    reducible_values theta v T_nat ->
    reducible_values theta (succ v) T_nat.
Proof.
  repeat step || simp_red.
Qed.

Lemma reducible_succ:
  forall theta t,
    valid_interpretation theta ->
    reducible theta t T_nat ->
    reducible theta (succ t) T_nat.
Proof.
  unfold reducible, reduces_to; steps.
  exists (succ t'); repeat step || simp_red; eauto with bsteplemmas.
Qed.

Lemma reducible_nat_value:
  forall theta v,
    is_nat_value v ->
    valid_interpretation theta ->
    reducible_values theta v T_nat.
Proof.
  induction v; repeat step;
    eauto using reducible_value_zero;
    eauto using reducible_values_succ.
Qed.

Lemma reducible_nat:
  forall theta v,
    is_nat_value v ->
    valid_interpretation theta ->
    reducible theta v T_nat.
Proof.
  induction v; repeat step;
    eauto using reducible_zero;
    eauto using reducible_succ.    
Qed.

Lemma open_reducible_succ:
  forall tvars gamma t,
    open_reducible tvars gamma t T_nat ->
    open_reducible tvars gamma (succ t) T_nat.
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
    valid_interpretation theta ->
    reducible theta tn T_nat ->
    (equivalent tn zero -> reducible theta t0 T) ->
     (forall n,
        equivalent tn (succ n) ->
        reducible_values theta n T_nat ->
        reducible
          theta
          (open 0 ts n)
          T) ->
    reducible theta (tmatch tn t0 ts) T.
Proof.
  steps.
  unfold reducible, reduces_to in H4; steps.
  eapply star_backstep_reducible with (tmatch _ t0 ts);
    repeat step || t_listutils || simp reducible_values in *;
      eauto with bsteplemmas;
      eauto with bwf;
      eauto with bfv.

  destruct t'; steps.

  - (* zero *)
    eapply backstep_reducible; eauto with smallstep;
      repeat step || t_listutils; eauto with b_equiv.
  - (* succ v *) 
    eapply backstep_reducible;
      repeat step || t_listutils || apply_any || apply reducible_nat_value;
      eauto 4 with smallstep values;
      auto 2 with bfv;
      eauto 2 with bwf;
      eauto 2 with b_equiv.
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
    open_reducible tvars gamma tn T_nat ->
    open_reducible tvars ((p, T_equal tn zero) :: gamma) t0 T ->
    open_reducible tvars (
        (p, T_equal tn (succ (fvar n))) ::
        (n, T_nat) ::
        gamma)
      (open 0 ts (fvar n))
      T ->
    open_reducible tvars gamma (tmatch tn t0 ts) T.
Proof.
  unfold open_reducible in *; repeat step || t_instantiate_sat3.  

  apply reducible_match; repeat step || t_termlist;
    eauto with bwf;
    eauto using subset_same with bfv.

  - (* zero *)
    unshelve epose proof (H12 theta ((p,trefl) :: lterms) _ _ _); tac1.
             
  - (* successor *)
    unshelve epose proof (H13 theta ((p,trefl) :: (n,n0) :: lterms) _ _ _); tac1.
Qed.

Lemma reducible_rec_induction:
  forall theta v t0 ts T,
    fv T = nil ->
    fv t0 = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf t0 0 ->
    wf ts 2 ->
    is_nat_value v ->
    valid_interpretation theta ->
    reducible theta t0 (open 0 T zero) ->
     (forall n tx,
        reducible_values theta n T_nat ->
        reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
        equivalent tx (lambda T_unit (rec T n t0 ts)) ->
        reducible theta
          (open 0 (open 1 ts n) tx)
          (open 0 T (succ n))) ->
    reducible theta (rec T v t0 ts) (T_let v T_nat T).
Proof.
  induction v; repeat step || simp_red || apply reducible_let.

  - (* zero *)
    eapply backstep_reducible; eauto with smallstep;
      repeat step || t_listutils.
  - (* succ v *) 
    eapply backstep_reducible; repeat step || t_listutils;
      eauto 3 with smallstep values;
      auto 2 with bfv;
      eauto 2 with bwf.

    apply H8;
      repeat step || unfold normalizing in * || t_listutils;
      eauto 2 with bfv;
      eauto 4 with bwf;
      eauto with values smallstep;
      eauto 2 with b_equiv;
      eauto using reducible_nat_value.

    apply reducible_lambda;
      repeat apply reducible_let || simp reducible_values ||
             apply reducible_intersection || tac1 ||
             (rewrite open_none by t_rewrite); eauto with btf.

    apply reducible_let2 with T_nat; eauto with values.
Qed.
      
Lemma reducible_rec:
  forall theta tn t0 ts T,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 2 ->
    valid_interpretation theta ->
    reducible theta tn T_nat ->
    reducible theta t0 (open 0 T zero) ->
     (forall tx n,
        reducible_values theta n T_nat ->
        reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
        equivalent tx (lambda T_unit (rec T n t0 ts)) ->
        reducible theta
          (open 0 (open 1 ts n) tx)
          (open 0 T (succ n))) ->
    reducible theta (rec T tn t0 ts) (T_let tn T_nat T).
Proof.
  repeat step.
  unfold reducible, reduces_to in H4; steps.
  eapply star_backstep_reducible with (rec T _ t0 ts);
    repeat step || t_listutils ||
      unshelve eauto with bsteplemmas ||
      unshelve eauto with bwf;
      unshelve eauto with bfv.

  eapply reducible_let_backstep_expr; eauto.
  apply reducible_rec_induction; repeat step || simp_red;
    repeat step; eauto with bfv bwf b_equiv.
Qed.

Lemma open_reducible_rec:
  forall tvars tn t0 ts gamma T n y p,
    wf T 1 ->
    wf ts 2 ->
    subset (fv T) (support gamma) ->
    subset (fv ts) (support gamma) ->
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
    NoDup (n :: y :: p :: nil) ->
    open_reducible tvars gamma tn T_nat ->
    open_reducible tvars gamma t0 (open 0 T zero) ->
    open_reducible tvars (
        (p, T_equal (fvar y) (lambda T_unit (rec T (fvar n) t0 ts))) ::
        (y, T_arrow T_unit (open 0 T (fvar n))) ::
        (n, T_nat) ::
        gamma)
      (open 0 (open 1 ts (fvar n)) (fvar y))
      (open 0 T (succ (fvar n))) ->
    open_reducible tvars gamma (rec T tn t0 ts) (T_let tn T_nat T).
Proof.
  unfold open_reducible in *; steps.  
    
  apply reducible_rec; repeat step;
    eauto with bwf;
    eauto with bfv;
    eauto with btf;
    try solve [ rewrite substitute_open2; eauto with bwf ].

  unshelve epose proof (H19 theta ((p,trefl) :: (y,tx) :: (n,n0) :: lterms) _ _ _);
      repeat tac1 || step_inversion NoDup || rewrite substitute_open in * || apply_any.
Qed.
