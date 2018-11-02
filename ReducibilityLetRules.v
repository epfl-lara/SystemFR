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
Require Import Termination.TypeForm.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Require Import Termination.TermList.
Require Import Termination.TermListLemmas.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTermList.

Require Import Termination.FVLemmas.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_val_let:
  forall A B a b,
    reducible_values a A ->
    reducible_values b (open 0 B a) ->
    reducible_values b (T_let a A B).
Proof.
  repeat step || simp reducible_values in *.
  eexists; eexists; steps; eauto with smallstep;
    eauto using red_is_val;
    eauto with btf.
Qed.

Lemma reducible_let:
  forall A B a b,
    reducible_values a A ->
    reducible b (open 0 B a) ->
    reducible b (T_let a A B).
Proof.
  steps.
  eauto using reducible_val_let, reducible_values_exprs.
Qed.
    
Lemma reducible_val_let2:
  forall A B a b,
    is_value a ->
    reducible_values b (T_let a A B) ->
    reducible_values b (open 0 B a).
Proof.
  repeat step || simp reducible_values in * || simp denote_values in * || t_values_info2 || t_invert_star.
Qed.

Lemma reducible_let2:
  forall A B a b,
    is_value a ->
    reducible b (T_let a A B) ->
    reducible b (open 0 B a).
Proof.
  eauto using reducible_val_let2, reducible_values_exprs.
Qed.

Lemma reducible_unused_let:
  forall a t A B,
    wf B 0 ->
    reducible_values a A ->
    reducible_values t (T_let a A B) ->
    reducible_values t B.
Proof.
  repeat step || simp reducible_values in * || t_values_info2 || t_invert_star.
  rewrite open_none in *; auto.
Qed.

Lemma reducible_unused_let_expr:
  forall a t A B,
    wf B 0 ->
    reducible_values a A ->
    reducible t (T_let a A B) ->
    reducible t B.
Proof.
  eauto using reducible_unused_let, reducible_values_exprs.
Qed.

Lemma reducible_let_smallstep_values:
  forall t1 t2 A B v,
    star small_step t1 t2 ->
    reducible_values v (T_let t1 A B) ->
    reducible_values v (T_let t2 A B).
Proof.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eexists; eexists; auto.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eauto using value_irred, star_many_steps.
Qed.
  
Lemma reducible_let_smallstep_expr:
  forall t1 t2 A B t,
    star small_step t1 t2 ->
    reducible t (T_let t1 A B) ->
    reducible t (T_let t2 A B).
Proof.
  eauto using reducible_let_smallstep_values, reducible_values_exprs.
Qed.

Lemma reducible_let_backstep_values:
  forall t1 t2 A B v,
    star small_step t1 t2 ->
    reducible_values v (T_let t2 A B) ->
    reducible_values v (T_let t1 A B).
Proof.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eexists.
  repeat step || simp reducible_values in * || simp denote_values in *.
  eauto using star_smallstep_trans.
Qed.
  
Lemma reducible_let_backstep_expr:
  forall t1 t2 A B t,
    star small_step t1 t2 ->
    reducible t (T_let t2 A B) ->
    reducible t (T_let t1 A B).
Proof.
  eauto using reducible_let_backstep_values, reducible_values_exprs.
Qed.


Lemma reducible_subtype_let_left:
  forall (gamma : context) (t : term) A B T x p v l,
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
    open_reducible gamma t A ->
    (forall (v : term) (l : list (nat * term)),
       satisfies reducible_values ((p, T_equal (fvar x) t) :: (x, A) :: gamma) l ->
       reducible_values v (substitute (open 0 B (fvar x)) l) ->
       reducible_values v (substitute T l)) ->
    satisfies reducible_values gamma l ->
    reducible_values v (T_let (substitute t l) (substitute A l) (substitute B l)) ->
    reducible_values v (substitute T l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || simp_red || tt || t_deterministic_star.
  unshelve epose proof (H11 v ((p,trefl) :: (x,t') :: l) _ _); tac1;
    eauto 3 using equivalent_sym with b_equiv.
Qed.

Lemma reducible_subtype_let_open:
  forall (gamma : context) (v : term) A B (t : term) (l : list (nat * term)),
    is_value v ->
    satisfies reducible_values gamma l ->
    reducible_values t (T_let (substitute v l) (substitute A l) (substitute B l)) ->
    reducible_values t (substitute (open 0 B v) l).
Proof.
  intros.
  rewrite substitute_open; eauto with bwf.
  eapply reducible_val_let2; eauto using is_value_subst, reducible_values_list.
Qed.

Lemma reducible_subtype_let_open2:
  forall (gamma : context) (v : term) A B,
    is_value v ->
    open_reducible gamma v A ->
    forall (t : term) (l : list (nat * term)),
      satisfies reducible_values gamma l ->
      reducible_values t (substitute (open 0 B v) l) ->
      reducible_values t (T_let (substitute v l) (substitute A l) (substitute B l)).
Proof.
  intros.
  unfold open_reducible in *; rewrite substitute_open in *; steps; eauto with bwf.
  eapply reducible_val_let;
    eauto using is_value_subst, reducible_values_list, reducible_expr_value;
    eauto 2 with btf.
Qed.
