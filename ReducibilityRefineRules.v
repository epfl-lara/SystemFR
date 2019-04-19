Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.TermProperties.
Require Import SystemFR.Sets.
Require Import SystemFR.TermList.
Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.StarInversions.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.SetLemmas.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.ReducibilityLetTermRules.
Require Import SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_refine:
  forall tvars gamma t A b x p,
    open_reducible tvars gamma t A ->
    wf b 1 ->
    wf t 0 ->
    subset (fv t) (support gamma) ->
    ~(p ∈ fv b) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv_context gamma) ->
    ~(x ∈ fv b) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv_context gamma) ->
    ~(x = p) ->
    is_erased_term b ->
    (forall theta l,
        valid_interpretation theta ->
        support theta = tvars ->
        satisfies (reducible_values theta) ((p,T_equal (term_fvar x) t) :: (x, A) :: gamma) l ->
        equivalent (substitute (open 0 b (term_fvar x)) l) ttrue) ->
    open_reducible tvars gamma t (T_refine A b).
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.

  unfold reducible, reduces_to in *; repeat step;
    eauto with bwf; eauto with bfv.

  eexists; steps; eauto.
  repeat step || simp_red; t_closer.

  unshelve epose proof (H12 theta ((p, uu) :: (x,t') :: lterms) _ _ _); tac1;
    eauto 3 using equivalent_sym with b_equiv;
    eauto using equivalent_true.
Qed.

Lemma reducible_refine_subtype:
  forall tvars theta (gamma : context) A B p q (x : nat) t l,
    wf q 1 ->
    is_erased_term q ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv q) ->
    open_reducible tvars ((x, B) :: gamma) (open 0 q (term_fvar x)) T_bool ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall l,
        satisfies (reducible_values theta) ((x, T_refine A p) :: gamma) l ->
        equivalent (substitute (open 0 q (term_fvar x)) l) ttrue) ->
    (forall t l,
        satisfies (reducible_values theta) gamma l ->
        reducible_values theta t (substitute A l) -> reducible_values theta t (substitute B l)) ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_refine (substitute A l) (substitute p l)) ->
    reducible_values theta t (T_refine (substitute B l) (substitute q l)).
Proof.
  repeat step || simp_red; eauto with bwf; eauto with berased.

  unshelve epose proof (H8 ((x,t) :: l) _); tac1;
    eauto using equivalent_true.
Qed.

Lemma reducible_refine_subtype2:
  forall theta (gamma : context) T A p (x : nat) t l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv p) ->
    is_erased_term p ->
    wf p 1 ->
    valid_interpretation theta ->
    (forall l,
        satisfies (reducible_values theta) ((x, T) :: gamma) l ->
        equivalent (substitute (open 0 p (term_fvar x)) l) ttrue) ->
    (forall t l,
        satisfies (reducible_values theta) gamma l ->
        reducible_values theta t (substitute T l) -> reducible_values theta t (substitute A l)) ->
      satisfies (reducible_values theta) gamma l ->
      reducible_values theta t (substitute T l) ->
      reducible_values theta t (T_refine (substitute A l) (substitute p l)).
Proof.
  repeat step || simp_red; t_closer.

  unshelve epose proof (H5 ((x,t) :: l) _); tac1;
    eauto using equivalent_true.
Qed.

Lemma reducible_refine_subtype3:
  forall tvars theta gamma T A b (x p : nat) t l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv b) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv b) ->
    ~(x = p) ->
    open_reducible tvars
                   ((p, T_equal (open 0 b (term_fvar x)) ttrue) :: (x, A) :: gamma)
                   (term_fvar x)
                   T ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_refine (substitute A l) (substitute b l)) ->
    reducible_values theta t (substitute T l).
Proof.
  unfold open_reducible; repeat step || simp_red; eauto with bwf.

  unshelve epose proof (H8 theta ((p, uu) :: (x,t) :: l) _ _ _); tac1;
    eauto using red_is_val, reducible_expr_value.
Qed.
