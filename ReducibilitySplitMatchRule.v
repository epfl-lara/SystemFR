Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.StarRelation.
Require Import SystemFR.Freshness.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.StarInversions.
Require Import SystemFR.Freshness.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.

Require Import SystemFR.TermList.
Require Import SystemFR.TermListLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.Sets.
Require Import SystemFR.SetLemmas.

Require Import SystemFR.Equivalence.
Require Import SystemFR.EquivalenceLemmas.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma equivalent_split_match:
  forall tvars theta (gamma1 gamma2 : context) n t t' e1 e2 e (x y v: nat) l,
    open_reducible tvars gamma2 n T_nat ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e1 -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e2 -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv n -> False) ->
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(v ∈ fv e) ->
    ~(v ∈ fv e1) ->
    ~(v ∈ fv e2) ->
    ~(v ∈ fv n) ->
    ~(v ∈ fv t) ->
    ~(v ∈ fv t') ->
    ~(v ∈ fv_context gamma1) ->
    ~(v ∈ fv_context gamma2) ->
    NoDup (x :: y :: v :: nil) ->
    subset (fv n ++ fv e1 ++ fv e2) (support gamma2) ->
    subset (fv e) (support gamma2) ->
    (forall l,
          satisfies (reducible_values theta)
                    (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal n zero) :: gamma2)
                    l ->
          equivalent (substitute t l) (substitute t' l)) ->
    (forall l,
          satisfies (reducible_values theta)
                    (gamma1 ++
                            (x, T_equal (open 0 e2 (term_fvar v)) e)
                            :: (y, T_equal n (succ (term_fvar v))) :: (v, T_nat) :: gamma2) l ->
          equivalent (substitute t l) (substitute t' l)) ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T_equal (tmatch n e1 e2) e) :: gamma2) l ->
    wf n 0 ->
    wf e1 0 ->
    wf e2 1 ->
    equivalent (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_listutils || t_sat_cut || t_instantiate_sat3 ||
           t_termlist || step_inversion satisfies ||
           simp_red.

  t_invert_nat_value; steps.

  - unshelve epose proof (H29 (l1 ++ (x, notype_trefl) :: (y, notype_trefl) :: lterms) _);
      repeat tac1 || step_inversion NoDup;
      eauto 2 using satisfies_drop.
  - unshelve epose proof (H30 (l1 ++ (x, notype_trefl) :: (y, notype_trefl) :: (v,v0) :: lterms) _);
      clear H29; clear H30; repeat tac1 || step_inversion NoDup;
      eauto 2 using satisfies_drop.
Qed.
