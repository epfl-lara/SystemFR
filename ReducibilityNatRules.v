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
Require Import Termination.TypeForm.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTermList.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTermList.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_zero:
  reducible zero T_nat.
Proof.
  unfold reducible, reduces_to;
    repeat step; eauto with step_tactic smallstep.
Qed.

Hint Resolve reducible_zero: breducible.

Lemma open_reducible_zero:
  forall gamma,
    open_reducible gamma zero T_nat.
Proof.
  unfold open_reducible in *; repeat step;
    auto using reducible_zero.
Qed.

Hint Resolve open_reducible_zero: breducible.


Lemma reducible_values_succ:
  forall v,
    reducible_values v T_nat ->
    reducible_values (succ v) T_nat.
Proof.
  steps.
Qed.

Lemma reducible_succ:
  forall t,
    reducible t T_nat ->
    reducible (succ t) T_nat.
Proof.
  unfold reducible, reduces_to; repeat step; eauto 4 with bsteplemmas.
Qed.

Hint Resolve reducible_succ: breducible.

Lemma reducible_nat_value:
  forall v,
    is_nat_value v ->
    reducible v T_nat.
Proof.
  induction v; repeat step; eauto with breducible.
Qed.

Hint Immediate reducible_nat_value: breducible.

Lemma open_reducible_succ:
  forall gamma t,
    open_reducible gamma t T_nat ->
    open_reducible gamma (succ t) T_nat.
Proof.
  unfold open_reducible in *; steps; eauto with breducible; eauto 3 with b_denote_rules.
Qed.

Hint Resolve open_reducible_succ: breducible.
      
Lemma reducible_match:
  forall tn t0 ts T,
    fv ts = nil ->
    fv t0 = nil ->
    wf t0 0 ->
    wf ts 1 ->
    reducible tn T_nat ->
    (equivalent tn zero -> reducible t0 T) ->
     (forall n,
        equivalent tn (succ n) ->
        reducible_values n T_nat ->
        reducible
          (open 0 ts n)
          T) ->
    reducible (tmatch tn t0 ts) T.
Proof.
  steps.
  unfold reducible, reduces_to in H3; steps.
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
      repeat step || t_listutils || apply_any;
      eauto 3 with smallstep values;
      auto 2 with bfv;
      eauto 2 with bwf;
      eauto 2 with b_equiv.
Qed.


Lemma open_reducible_match:
  forall tn t0 ts gamma T n p,
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
    open_reducible gamma tn T_nat ->
    open_reducible ((p, T_equal tn zero) :: gamma) t0 T ->
    open_reducible (
        (p, T_equal tn (succ (fvar n))) ::
        (n, T_nat) ::
        gamma)
      (open 0 ts (fvar n))
      T ->
    open_reducible gamma (tmatch tn t0 ts) T.
Proof.
  unfold open_reducible in *; repeat step.  

  apply reducible_match; repeat step;
    eauto with bwf;
    eauto with bfv.

  - (* zero *)
    unshelve epose proof (H12 ((p,trefl) :: l) _); tac1.
             
  - (* successor *)
    unshelve epose proof (H13 ((p,trefl) :: (n,n0) :: l) _); tac1.
Qed.

Lemma reducible_rec_induction:
  forall v t0 ts T,
    fv T = nil ->
    fv t0 = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf t0 0 ->
    wf ts 2 ->
    is_nat_value v ->
    reducible t0 (open 0 T zero) ->
     (forall n tx,
        reducible_values n T_nat ->
        reducible_values tx (T_arrow T_unit (open 0 T n)) ->
        equivalent tx (lambda T_unit (rec T n t0 ts)) ->
        reducible
          (open 0 (open 1 ts n) tx)
          (open 0 T (succ n))) ->
    reducible (rec T v t0 ts) (T_let v T_nat T).
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

    apply_any; repeat step || unfold normalizing in * || t_listutils;
      eauto 2 with bfv;
      eauto 4 with bwf;
      eauto with values smallstep;
      eauto 2 with b_equiv.

    apply reducible_lambda;
      repeat apply reducible_let || simp reducible_values ||
             apply reducible_intersection || tac1 ||
             (rewrite open_none by t_rewrite); eauto with btf.

    apply reducible_let2 with T_nat; eauto with values.
Qed.
      
Lemma reducible_rec:
  forall tn t0 ts T,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 2 ->
    reducible tn T_nat ->
    reducible t0 (open 0 T zero) ->
     (forall tx n,
        reducible_values n T_nat ->
        reducible_values tx (T_arrow T_unit (open 0 T n)) ->
        equivalent tx (lambda T_unit (rec T n t0 ts)) ->
        reducible
          (open 0 (open 1 ts n) tx)
          (open 0 T (succ n))) ->
    reducible (rec T tn t0 ts) (T_let tn T_nat T).
Proof.
  repeat step.
  unfold reducible, reduces_to in H3; steps.
  eapply star_backstep_reducible with (rec T _ t0 ts);
    repeat step || t_listutils ||
      unshelve eauto with bsteplemmas ||
      unshelve eauto with bwf;
      unshelve eauto with bfv.

  eapply reducible_let_backstep_expr; eauto.
  apply reducible_rec_induction; steps;
    repeat step; eauto with bfv bwf b_equiv.
Qed.
  
Lemma open_reducible_rec:
  forall tn t0 ts gamma T n y p,
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
    open_reducible gamma tn T_nat ->
    open_reducible gamma t0 (open 0 T zero) ->
    open_reducible (
        (p, T_equal (fvar y) (lambda T_unit (rec T (fvar n) t0 ts))) ::
        (y, T_arrow T_unit (open 0 T (fvar n))) ::
        (n, T_nat) ::
        gamma)
      (open 0 (open 1 ts (fvar n)) (fvar y))
      (open 0 T (succ (fvar n))) ->
    open_reducible gamma (rec T tn t0 ts) (T_let tn T_nat T).
Proof.
  unfold open_reducible in *; steps.  
    
  apply reducible_rec; repeat step;
    eauto with bwf;
    eauto with bfv;
    eauto with btf;
    try solve [ rewrite substitute_open2; eauto with bwf ].

  unshelve epose proof (H19 ((p,trefl) :: (y,tx) :: (n,n0) :: l) _);
      repeat tac1 || step_inversion NoDup || rewrite substitute_open in * || apply_any.
Qed.
