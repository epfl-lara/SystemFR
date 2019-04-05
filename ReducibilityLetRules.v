Require Import Coq.Strings.String.

Require Import Equations.Equations.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.Sets.
Require Import SystemFR.SetLemmas.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.ListUtils.
Require Import SystemFR.Freshness.
Require Import SystemFR.AssocList.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.

Require Import SystemFR.TermList.
Require Import SystemFR.TermListLemmas.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.FVLemmas.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_val_let:
  forall theta A B a b,
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible_values theta b (open 0 B a) ->
    reducible_values theta b (T_let a B).
Proof.
  repeat step || simp reducible_values in *; eauto using reducible_values_closed.
  exists a; steps; eauto using red_is_val; eauto with berased.
Qed.

Lemma reducible_let:
  forall theta A B a b,
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible theta b (open 0 B a) ->
    reducible theta b (T_let a B).
Proof.
  steps.
  eauto using reducible_val_let, reducible_values_exprs.
Qed.

Lemma reducible_val_let2:
  forall theta B a b,
    valid_interpretation theta ->
    is_value a ->
    reducible_values theta b (T_let a B) ->
    reducible_values theta b (open 0 B a).
Proof.
  repeat step || simp reducible_values in * || t_values_info2 || t_invert_star.
Qed.

Lemma reducible_let2:
  forall theta B a b,
    valid_interpretation theta ->
    is_value a ->
    reducible theta b (T_let a B) ->
    reducible theta b (open 0 B a).
Proof.
  eauto using reducible_val_let2, reducible_values_exprs.
Qed.

Lemma reducible_unused_let:
  forall theta a t A B,
    wf B 0 ->
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible_values theta t (T_let a B) ->
    reducible_values theta t B.
Proof.
  repeat step || simp reducible_values in * || t_values_info2 || t_invert_star.
  rewrite open_none in *; auto.
Qed.

Lemma reducible_unused_let_expr:
  forall theta a t A B,
    wf B 0 ->
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible theta t (T_let a B) ->
    reducible theta t B.
Proof.
  eauto using reducible_unused_let, reducible_values_exprs.
Qed.

Lemma reducible_let_smallstep_values:
  forall theta t1 t2 B v,
    star small_step t1 t2 ->
    reducible_values theta v (T_let t1 B) ->
    reducible_values theta v (T_let t2 B).
Proof.
  repeat step || simp reducible_values in *.
  exists a'; steps; eauto with berased.
  eauto using value_irred, star_many_steps.
Qed.

Lemma reducible_let_smallstep_expr:
  forall theta t1 t2 B t,
    valid_interpretation theta ->
    star small_step t1 t2 ->
    reducible theta t (T_let t1 B) ->
    reducible theta t (T_let t2 B).
Proof.
  eauto using reducible_let_smallstep_values, reducible_values_exprs.
Qed.

Lemma reducible_let_backstep_values:
  forall theta t1 t2 B v,
    valid_interpretation theta ->
    is_erased_term t1 ->
    star small_step t1 t2 ->
    reducible_values theta v (T_let t2 B) ->
    reducible_values theta v (T_let t1 B).
Proof.
  repeat step || simp reducible_values in *.
  exists a'; steps; eauto using star_smallstep_trans.
Qed.

Lemma reducible_let_backstep_expr:
  forall theta t1 t2 B t,
    valid_interpretation theta ->
    is_erased_term t1 ->
    star small_step t1 t2 ->
    reducible theta t (T_let t2 B) ->
    reducible theta t (T_let t1 B).
Proof.
  eauto using reducible_let_backstep_values, reducible_values_exprs.
Qed.


Lemma reducible_subtype_let_left:
  forall tvars theta (gamma : context) t A B T x p v l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv t) ->
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv B) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv t) ->
    ~(x = p) ->
    open_reducible tvars gamma t A ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall v l,
       satisfies (reducible_values theta) ((p, T_equal (term_fvar x) t) :: (x, A) :: gamma) l ->
       reducible_values theta v (substitute (open 0 B (term_fvar x)) l) ->
       reducible_values theta v (substitute T l)) ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta v (T_let (substitute t l) (substitute B l)) ->
    reducible_values theta v (substitute T l).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || simp_red || t_instantiate_sat3 || t_deterministic_star.
  unshelve epose proof (H13 v ((p, notype_trefl) :: (x,t') :: l) _ _); tac1;
    eauto 3 using equivalent_sym with b_equiv.
Qed.

Lemma reducible_subtype_let_open:
  forall theta (gamma : context) v B t l,
    is_value v ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_let (substitute v l) (substitute B l)) ->
    reducible_values theta t (substitute (open 0 B v) l).
Proof.
  steps.
  rewrite substitute_open; eauto with bwf.
  eapply reducible_val_let2; eauto using is_value_subst, reducible_values_list.
Qed.

Lemma reducible_subtype_let_open2:
  forall tvars theta (gamma : context) v A B,
    is_value v ->
    open_reducible tvars gamma v A ->
    valid_interpretation theta ->
    support theta = tvars ->
    forall t l,
      satisfies (reducible_values theta) gamma l ->
      reducible_values theta t (substitute (open 0 B v) l) ->
      reducible_values theta t (T_let (substitute v l) (substitute B l)).
Proof.
  steps.
  unfold open_reducible in *; rewrite substitute_open in *; steps; eauto with bwf.
  eapply reducible_val_let;
    eauto using is_value_subst, reducible_values_list, reducible_expr_value;
    eauto 2 with btf.
Qed.
