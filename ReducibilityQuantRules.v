Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.ListUtils.
Require Import SystemFR.Sets.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.TermList.
Require Import SystemFR.StarRelation.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.StarInversions.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.ReducibilityLetTermRules.
Require Import SystemFR.RedTactics.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_forall:
  forall theta t U V A,
    valid_interpretation theta ->
    reducible theta t A ->
    wf U 0 ->
    fv U = nil ->
    is_erased_type V ->
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
    t_closer.
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
    is_erased_type V ->
    open_reducible tvars ((x, U) :: gamma) t (open 0 V (term_fvar x)) ->
    open_reducible tvars gamma t (T_forall U V).
Proof.
  unfold open_reducible in *; repeat step || t_instantiate_sat3.

  eapply reducible_forall; steps; t_closer.
  unshelve epose proof (H8 theta ((x,u) :: lterms) _ _ _); tac1.
Qed.

Lemma open_reducible_exists_elim:
  forall tvars (gamma : context) p U V t T u v,
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
    is_erased_term t ->
    subset (fv U) (support gamma) ->
    subset (fv V) (support gamma) ->
    subset (fv t) (support gamma) ->
    open_reducible tvars gamma p (T_exists U V) ->
    open_reducible tvars
                   ((v, open 0 V (term_fvar u)) :: (u, U) :: gamma)
                   (open 0 t (term_fvar v)) T ->
    open_reducible tvars gamma (notype_tlet p t) T.
Proof.
  unfold open_reducible; repeat step || t_instantiate_sat3.
  pose proof H5 as Copy.
  unfold reducible, reduces_to in H5.
  repeat step || t_instantiate_sat3 || t_listutils || simp_red || t_deterministic_star ||
         apply reducible_let_rule with
             (T_exists (psubstitute U lterms term_var) (psubstitute V lterms term_var)); t_closer.

  unshelve epose proof (H18 theta ((v,v0) :: (u,a) :: lterms) _ _ _); tac1.
Qed.

Set Program Mode.

Lemma reducible_subtype_forall:
  forall tvars theta (gamma : context) t T1 T2 t0 l,
    open_reducible tvars gamma t T1 ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t0 (T_forall (substitute T1 l) (substitute T2 l)) ->
    reducible_values theta t0 (T_let (substitute t l) (substitute T2 l)).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_instantiate_sat3 || simp_red.

  unshelve exists t'; steps; t_closer.
Qed.

Lemma reducible_subtype_exists:
  forall tvars theta (gamma : context) t T1 T2 t0 l,
    open_reducible tvars gamma t T1 ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta t0 (T_let (substitute t l) (substitute T2 l)) ->
    reducible_values theta t0 (T_exists (substitute T1 l) (substitute T2 l)).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || t_deterministic_star; eauto.
Qed.

Lemma open_reducible_forall_inst:
  forall (tvars : list nat) (gamma : context) (t1 t2 U V : tree),
    is_erased_term t1 ->
    is_erased_term t2 ->
    wf t1 0 ->
    wf t2 0 ->
    subset (pfv t1 term_var) (support gamma) ->
    subset (pfv t2 term_var) (support gamma) ->
    open_reducible tvars gamma t1 (T_forall U V) ->
    open_reducible tvars gamma t2 U ->
    open_reducible tvars gamma t1 (T_let t2 V).
Proof.
  repeat step || unfold open_reducible, reducible, reduces_to in * || simp_red ||
         t_instantiate_sat3 || find_smallstep_value;
    try t_closing;
    eauto with bfv bwf.
Qed.
