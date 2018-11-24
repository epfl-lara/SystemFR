Require Import Equations.Equations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityArrowRules.
Require Import Termination.ReducibilityNatRules.
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
Require Import Termination.SetLemmas.
Require Import Termination.SubstitutionErase.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Opaque reducible_values.
Opaque makeFresh.


Lemma reducible_fix_induction:
  forall theta T v ts,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_nat_value v ->
    is_erased_term ts ->
    valid_interpretation theta ->
    (forall tx, reducible_values theta tx T_top -> reducible theta (open 0 ts tx) (open 0 T zero)) ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
       equivalent tx (notype_lambda (notype_tfix ts)) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T (succ n))) ->
    reducible theta (notype_tfix ts) (T_let v T_nat T).
Proof.
  induction v; repeat step || simp_red || apply reducible_let.

  - (* zero *)
    eapply backstep_reducible; eauto with smallstep;
      repeat step || t_listutils || apply_any || simp_red;
      t_closer.
  - (* succ v *)
    eapply backstep_reducible; repeat step || t_listutils || apply_any;
      eauto 3 with smallstep values;
      eauto with bfv;
      eauto 2 with bwf;
      eauto with berased;
      eauto using reducible_nat_value;
      eauto 2 with b_equiv.

    apply reducible_lambda;
      repeat apply reducible_let || simp reducible_values ||
             apply reducible_intersection || tac1 ||
             (rewrite open_none by t_rewrite); eauto with berased.

    apply reducible_let2 with T_nat; eauto with values.
Qed.


Lemma reducible_fix:
  forall theta tn ts T,
    fv T = nil ->
    fv ts = nil ->
    wf T 1 ->
    wf ts 1 ->
    is_erased_term ts ->
    valid_interpretation theta ->
    reducible theta tn T_nat ->
    (forall tx, reducible_values theta tx T_top -> reducible theta (open 0 ts tx) (open 0 T zero)) ->
    (forall tx n,
       reducible_values theta n T_nat ->
       reducible_values theta tx (T_arrow T_unit (open 0 T n)) ->
       equivalent tx (notype_lambda (notype_tfix ts)) ->
       reducible theta
         (open 0 ts tx)
         (open 0 T (succ n))) ->
    reducible theta (notype_tfix ts) (T_let tn T_nat T).
Proof.
  repeat step.
  unfold reducible, reduces_to in H5; steps.

  eapply reducible_let_backstep_expr; eauto; t_closer.
  apply reducible_fix_induction; repeat step || simp_red;
    repeat step; eauto with bfv bwf b_equiv.
Qed.

Lemma open_reducible_fix:
  forall tvars tn ts gamma T n y p,
    wf T 1 ->
    wf ts 1 ->
    subset (fv T) (support gamma) ->
    subset (fv ts) (support gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv_context gamma) ->
    ~(y ∈ fv ts) ->
    ~(y ∈ fv T) ->
    ~(y ∈ fv_context gamma) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    is_erased_term ts ->
    NoDup (n :: y :: p :: nil) ->
    open_reducible tvars gamma tn T_nat ->
    open_reducible tvars ((y, T_top) :: gamma) (open 0 ts (fvar y term_var)) (open 0 T zero) ->
    open_reducible tvars (
        (p, T_equal (fvar y term_var) (notype_lambda (notype_tfix ts))) ::
        (y, T_arrow T_unit (open 0 T (fvar n term_var))) ::
        (n, T_nat) ::
        gamma)
      (open 0 ts (fvar y term_var))
      (open 0 T (succ (fvar n term_var))) ->
    open_reducible tvars gamma (notype_tfix ts) (T_let tn T_nat T).
Proof.
  unfold open_reducible in *; steps.

  apply reducible_fix; repeat step;
    eauto with bwf;
    eauto with bfv;
    eauto with berased;
    try solve [ rewrite substitute_open2; eauto with bwf ].

  - unshelve epose proof (H16 theta ((y,tx) :: lterms) _ _ _);
      repeat tac1 || step_inversion NoDup || rewrite substitute_open in * || apply_any.

  - unshelve epose proof (H17 theta ((p,trefl) :: (y,tx) :: (n,n0) :: lterms) _ _ _);
      repeat tac1 || step_inversion NoDup || rewrite substitute_open in * || apply_any.
Qed.
