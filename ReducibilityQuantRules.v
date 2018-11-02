Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.ListUtils.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TermList.
Require Import Termination.StarRelation.
Require Import Termination.StarLemmas.
Require Import Termination.SmallStep.
Require Import Termination.SmallStepSubstitutions.
Require Import Termination.StarInversions.
Require Import Termination.TermForm.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityLetTermRules.
Require Import Termination.RedTactics.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_forall:
  forall theta t U V A,
    valid_interpretation theta ->
    reducible theta t A ->
    wf U 0 ->
    fv U = nil ->
    (forall u, reducible_values theta u U -> reducible theta t (open 0 V u)) ->
    reducible theta t (T_forall U V).
Proof.
  unfold reducible, reduces_to;
  repeat step || t_listutils || unfold reducible, reduces_to || simp reducible_values in * ||
         rewrite reducibility_rewrite;
    eauto 2 with bsteplemmas;
    eauto with bfv bwf;
    eauto using red_is_val.

  exists t'; repeat step || simp_red || t_deterministic_star || instantiate_any;
    eauto using red_is_val; eauto with bwf bfv.
Qed.

Lemma open_reducible_forall:
  forall tvars gamma x t U V A,
    ~(x ∈ fv t) ->
    ~(x ∈ fv U) ->
    ~(x ∈ fv V) ->
    ~(x ∈ fv_context gamma) ->
    open_reducible tvars gamma t A ->
    wf U 0 ->
    subset (fv U) (support gamma) ->
    subset (fv t) (support gamma) ->
    open_reducible tvars ((x, U) :: gamma) t (open 0 V (fvar x)) ->
    open_reducible tvars gamma t (T_forall U V).
Proof.
  unfold open_reducible in *; repeat step || t_instantiate_sat3.

  eapply reducible_forall; steps;
    eauto with bwf;
    eauto with bfv sets btermlist;
    eauto with values;
    eauto with btf.
  unshelve epose proof (H7 theta ((x,u) :: lterms) _ _ _); tac1.
Qed.

Lemma open_reducible_exists_elim:
  forall tvars (gamma : context) (p : term) U V (t : term) T u v,
    ~(u ∈ fv_context gamma) ->
    ~(u ∈ fv t) ->
    ~(u ∈ fv U) ->
    ~(u ∈ fv V) ->
    ~(u ∈ fv T) ->
    ~(v ∈ fv_context gamma) ->
    ~(u ∈ fv t) ->
    ~(v ∈ fv U) ->
    ~(v ∈ fv V) ->
    ~(v ∈ fv T) ->
    ~(u = v) ->
    wf U 0 ->
    wf V 1 ->
    wf t 1 ->
    subset (fv U) (support gamma) ->
    subset (fv V) (support gamma) ->
    subset (fv t) (support gamma) ->
    open_reducible tvars gamma p (T_exists U V) ->
    open_reducible tvars ((v, open 0 V (fvar u)) :: (u, U) :: gamma) (open 0 t (fvar v)) T ->
    open_reducible tvars gamma (tlet p (T_exists U V) t) T.
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  pose proof H5 as Copy.
  unfold reducible, reduces_to in H5.
  repeat step || t_instantiate_sat3 || t_listutils || simp_red || t_deterministic_star || apply reducible_let_rule;
    eauto with bwf; eauto with bfv.

  unshelve epose proof (H17 theta ((v,v0) :: (u,a) :: lterms) _ _ _); tac1.
Qed.

Lemma reducible_subtype_forall:
  forall tvars theta (gamma : context) (t : term) T1 T2 t0 l,
    open_reducible tvars gamma t T1 ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t0 (T_forall (substitute T1 l) (substitute T2 l)) ->
    reducible_values theta t0 (T_let (substitute t l) (substitute T1 l) (substitute T2 l)).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || t_instantiate_sat3 || simp_red;
    eauto 9 using red_is_val with btf.
Qed.

Lemma reducible_subtype_exists:
  forall tvars theta (gamma : context) (t : term) T1 T2 t0 l,
    open_reducible tvars gamma t T1 ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t0 (T_let (substitute t l) (substitute T1 l) (substitute T2 l)) ->
    reducible_values theta t0 (T_exists (substitute T1 l) (substitute T2 l)).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || t_deterministic_star; eauto.
Qed. 
