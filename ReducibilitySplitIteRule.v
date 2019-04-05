Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.StarRelation.
Require Import SystemFR.Freshness.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.ListUtils.
Require Import SystemFR.StarInversions.
Require Import SystemFR.Freshness.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.SmallStepSubstitutions.
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

Require Import SystemFR.RedTactics.
Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.

Opaque reducible_values.
Opaque makeFresh.

Lemma equivalent_split_ite:
  forall tvars theta (gamma1 gamma2 : context) b e1 e2 t t' e (x y : nat) l,
    open_reducible tvars gamma2 b T_bool ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e1 -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e2 -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv e -> False) ->
    (forall z, z ∈ support gamma1 -> z ∈ fv b -> False) ->
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(y ∈ fv b) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(x = y) ->
    subset (fv b ++ fv e1 ++ fv e2) (support gamma2) ->
    subset (fv e) (support gamma2) ->
    wf e 0 ->
    wf b 0 ->
    wf e1 0 ->
    wf e2 0 ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equal e1 e) :: (y, T_equal b ttrue) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equal e2 e) :: (y, T_equal b tfalse) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T_equal (ite b e1 e2) e) :: gamma2) l ->
    equivalent (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_listutils || t_sat_cut || t_instantiate_sat3 || t_termlist || step_inversion satisfies ||
           simp_red.

    - unshelve epose proof (H24 (l1 ++ (x, notype_trefl) :: (y, notype_trefl) :: lterms) _); tac1;
        eauto 2 using satisfies_drop.
    - unshelve epose proof (H25 (l1 ++ (x, notype_trefl) :: (y, notype_trefl) :: lterms) _); tac1;
        eauto 2 using satisfies_drop.
Qed.
