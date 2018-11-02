Require Import Equations.Equations.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.SmallStep.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.StarLemmas.
Require Import Termination.StarInversions.
Require Import Termination.SmallStepSubstitutions.

Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTermList.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTermList.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.ReducibilityLetRules.
Require Import Termination.ReducibilityLetTermRules.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_refine:
  forall gamma t A b x p,
    open_reducible gamma t A ->
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
    (forall l, satisfies reducible_values ((p,T_equal (fvar x) t) :: (x, A) :: gamma) l ->
          equivalent (substitute (open 0 b (fvar x)) l) ttrue) ->
    open_reducible gamma t (T_refine A b).
Proof.
  unfold open_reducible; repeat step || instantiate_any.

  unfold reducible, reduces_to in *; repeat step;
    eauto with bwf; eauto with bfv.

  eexists; steps; eauto.
  repeat step || simp reducible_values in *; eauto with bwf.

  unshelve epose proof (H11 ((p,trefl) :: (x,t') :: l) _); tac1;
    eauto 3 using equivalent_sym with b_equiv;
    eauto using equivalent_true.
Qed.

Hint Resolve reducible_refine: breducible.

Lemma reducible_refine_subtype:
  forall (gamma : context) A B (p q : term) (x : nat) t l,
    wf q 1 ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv p) ->
    ~(x ∈ fv q) ->
    open_reducible ((x, B) :: gamma) (open 0 q (fvar x)) T_bool ->
    (forall l : list (nat * term),
        satisfies reducible_values ((x, T_refine A p) :: gamma) l ->
        equivalent (substitute (open 0 q (fvar x)) l) ttrue) ->
    (forall (t : term) (l : list (nat * term)),
        satisfies reducible_values gamma l ->
        reducible_values t (substitute A l) -> reducible_values t (substitute B l)) ->
    satisfies reducible_values gamma l ->
    reducible_values t (T_refine (substitute A l) (substitute p l)) ->
    reducible_values t (T_refine (substitute B l) (substitute q l)).
Proof.
  repeat step || simp_red; eauto with bwf.

  unshelve epose proof (H5 ((x,t) :: l) _); tac1;
    eauto using equivalent_true.
Qed.

Lemma reducible_refine_subtype2:
  forall (gamma : context) T A (p : term) (x : nat) t l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv p) ->
    wf p 1 ->
    (forall l : list (nat * term),
        satisfies reducible_values ((x, T) :: gamma) l ->
        equivalent (substitute (open 0 p (fvar x)) l) ttrue) ->
    (forall (t : term) (l : list (nat * term)),
        satisfies reducible_values gamma l ->
        reducible_values t (substitute T l) -> reducible_values t (substitute A l)) ->
      satisfies reducible_values gamma l ->
      reducible_values t (substitute T l) ->
      reducible_values t (T_refine (substitute A l) (substitute p l)).
Proof.
  repeat step || simp_red; eauto with bwf.

  unshelve epose proof (H3 ((x,t) :: l) _); tac1;
    eauto using equivalent_true.
Qed.

Lemma reducible_refine_subtype3:
  forall gamma T A (b : term) (x p : nat) t l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv A) ->
    ~(p ∈ fv T) ->
    ~(p ∈ fv b) ->
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv b) ->
    ~(x = p) ->
    open_reducible ((p, T_equal (open 0 b (fvar x)) ttrue) :: (x, A) :: gamma) (fvar x) T ->
    satisfies reducible_values gamma l ->
    reducible_values t (T_refine (substitute A l) (substitute b l)) ->
    reducible_values t (substitute T l).
Proof.
  unfold open_reducible; repeat step || simp_red; eauto with bwf.

  unshelve epose proof (H8 ((p,trefl) :: (x,t) :: l) _); tac1;
      eauto using red_is_val, reducible_expr_value.
Qed.
