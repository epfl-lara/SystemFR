Require Import Coq.Strings.String.

Require Import Equations.Equations.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.SmallStep.
Require Import Termination.StarInversions.
Require Import Termination.StarRelation.
Require Import Termination.StarLemmas.
Require Import Termination.SizeLemmas.
Require Import Termination.Sets.
Require Import Termination.SetLemmas.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.SmallStepSubstitutions.
Require Import Termination.ListUtils.
Require Import Termination.Freshness.
Require Import Termination.TermForm.
Require Import Termination.AssocList.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Require Import Termination.TermList.
Require Import Termination.TermListLemmas.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Require Import Termination.FVLemmas.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_val_let:
  forall theta A B a b,
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible_values theta b (open 0 B a) ->
    reducible_values theta b (T_let a A B).
Proof.
  repeat step || simp reducible_values in *.
  eexists; eexists; steps; eauto with smallstep;
    eauto using red_is_val;
    eauto with btf.
Qed.

Lemma reducible_let:
  forall theta A B a b,
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible theta b (open 0 B a) ->
    reducible theta b (T_let a A B).
Proof.
  steps.
  eauto using reducible_val_let, reducible_values_exprs.
Qed.
    
Lemma reducible_val_let2:
  forall theta A B a b,
    valid_interpretation theta ->
    is_value a ->
    reducible_values theta b (T_let a A B) ->
    reducible_values theta b (open 0 B a).
Proof.
  repeat step || simp reducible_values in * || simp denote_values in * || t_values_info2 || t_invert_star.
Qed.

Lemma reducible_let2:
  forall theta A B a b,
    valid_interpretation theta ->
    is_value a ->
    reducible theta b (T_let a A B) ->
    reducible theta b (open 0 B a).
Proof.
  eauto using reducible_val_let2, reducible_values_exprs.
Qed.

Lemma reducible_unused_let:
  forall theta a t A B,
    wf B 0 ->
    valid_interpretation theta ->
    reducible_values theta a A ->
    reducible_values theta t (T_let a A B) ->
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
    reducible theta t (T_let a A B) ->
    reducible theta t B.
Proof.
  eauto using reducible_unused_let, reducible_values_exprs.
Qed.

Lemma reducible_let_smallstep_values:
  forall theta t1 t2 A B v,
    star small_step t1 t2 ->
    reducible_values theta v (T_let t1 A B) ->
    reducible_values theta v (T_let t2 A B).
Proof.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eexists; eexists; auto.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eauto using value_irred, star_many_steps.
Qed.
  
Lemma reducible_let_smallstep_expr:
  forall theta t1 t2 A B t,
    valid_interpretation theta ->
    star small_step t1 t2 ->
    reducible theta t (T_let t1 A B) ->
    reducible theta t (T_let t2 A B).
Proof.
  eauto using reducible_let_smallstep_values, reducible_values_exprs.
Qed.

Lemma reducible_let_backstep_values:
  forall theta t1 t2 A B v,
    valid_interpretation theta ->
    star small_step t1 t2 ->
    reducible_values theta v (T_let t2 A B) ->
    reducible_values theta v (T_let t1 A B).
Proof.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eexists.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eauto using star_smallstep_trans.
Qed.
  
Lemma reducible_let_backstep_expr:
  forall theta t1 t2 A B t,
    valid_interpretation theta ->
    star small_step t1 t2 ->
    reducible theta t (T_let t2 A B) ->
    reducible theta t (T_let t1 A B).
Proof.
  eauto using reducible_let_backstep_values, reducible_values_exprs.
Qed.


Lemma reducible_subtype_let_left:
  forall tvars theta (gamma : context) (t : term) A B T x p v l,
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
    (forall (v : term) (l : list (nat * term)),
       satisfies (reducible_values theta) ((p, T_equal (term_fvar x) t) :: (x, A) :: gamma) l ->
       reducible_values theta v (substitute (open 0 B (term_fvar x)) l) ->
       reducible_values theta v (substitute T l)) ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta v (T_let (substitute t l) (substitute A l) (substitute B l)) ->
    reducible_values theta v (substitute T l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || simp_red || t_instantiate_sat3 || t_deterministic_star.
  unshelve epose proof (H13 v ((p,trefl) :: (x,t') :: l) _ _); tac1;
    eauto 3 using equivalent_sym with b_equiv.
Qed.

Lemma reducible_subtype_let_open:
  forall theta (gamma : context) (v : term) A B (t : term) (l : list (nat * term)),
    is_value v ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t (T_let (substitute v l) (substitute A l) (substitute B l)) ->
    reducible_values theta t (substitute (open 0 B v) l).
Proof.
  steps.
  rewrite substitute_open; eauto with bwf.
  eapply reducible_val_let2; eauto using is_value_subst, reducible_values_list.
Qed.

Lemma reducible_subtype_let_open2:
  forall tvars theta (gamma : context) (v : term) A B,
    is_value v ->
    open_reducible tvars gamma v A ->
    valid_interpretation theta ->
    support theta = tvars ->
    forall (t : term) (l : list (nat * term)),
      satisfies (reducible_values theta) gamma l ->
      reducible_values theta t (substitute (open 0 B v) l) ->
      reducible_values theta t (T_let (substitute v l) (substitute A l) (substitute B l)).
Proof.
  steps.
  unfold open_reducible in *; rewrite substitute_open in *; steps; eauto with bwf.
  eapply reducible_val_let;
    eauto using is_value_subst, reducible_values_list, reducible_expr_value;
    eauto 2 with btf.
Qed.
