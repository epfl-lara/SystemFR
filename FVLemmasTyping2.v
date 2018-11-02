Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.
Require Import Termination.Typing.
Require Import Termination.AssocList.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Freshness.
Require Import Termination.ListUtils.
Require Import Termination.SmallStep.
Require Import Termination.TermList.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasEval.
Require Import Termination.FVLemmasTyping.


Lemma defined_FV_HT_1_open:
  forall tvars gamma t T k rep,
    has_type tvars gamma (open k t rep) T ->
    subset (fv t) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open.
Qed.

Hint Resolve defined_FV_HT_1_open: bfv2.

Lemma defined_FV_HT_2_open:
  forall tvars gamma t T k rep,
    has_type tvars gamma t (open k T rep) ->
    subset (fv T) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open.
Qed.

Hint Resolve defined_FV_HT_2_open: bfv2.

Lemma defined_FV_HT_1_open_3_2:
  forall tvars gamma t T i j x y z X Y Z rep1 rep2,
    ~(x ∈ fv t) ->
    ~(y ∈ fv t) ->
    ~(z ∈ fv t) ->
    has_type tvars
             ((x,X) :: (y,Y) :: (z,Z) :: gamma)
             (open i (open j t rep1) rep2) T ->
    subset (fv t) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_FV_HT_1_open_3_2: bfv2.

Lemma defined_FV_HT_1_open_2_1:
  forall tvars gamma t T i x y X Y rep,
    ~(x ∈ fv t) ->
    ~(y ∈ fv t) ->
    has_type tvars
             ((x,X) :: (y,Y) :: gamma)
             (open i t rep) T ->
    subset (fv t) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_FV_HT_1_open_2_1: bfv2.

Lemma defined_FV_HT_1_var:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    x ∈ fv t ->
    (x ∈ support gamma).
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_FV_HT_1_var: bfv2.

Lemma defined_FV_HT_1_var_neg:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    (x ∈ support gamma -> False) ->
    (x ∈ fv t -> False).
Proof.
  intros tvars gamma t T x H1 H2 H.
  pose proof (defined_FV_HT_1_var _ _ _ _ _ H1 H); steps.
Qed.

Hint Resolve defined_FV_HT_1_var_neg: bfv2.

Lemma defined_FV_HT_2_var:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    x ∈ fv T ->
    x ∈ support gamma.
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_FV_HT_2_var: bfv2.

Lemma defined_FV_HT_2_var_neg:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    (x ∈ support gamma -> False) ->
    (x ∈ fv T -> False).
Proof.
  intros tvars gamma t T x H1 H2 H.
  pose proof (defined_FV_HT_2_var _ _ _ _ _ H1 H); steps.
Qed.

Hint Resolve defined_FV_HT_2_var_neg: bfv2.

Lemma defined_FV_IT_var:
  forall tvars gamma T x,
    is_type tvars gamma T ->
    x ∈ fv T ->
    x ∈ support gamma.
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_FV_IT_var: bfv2.

Lemma defined_FV_IT_var_neg:
  forall tvars gamma T x,
    is_type tvars gamma T ->
    (x ∈ support gamma -> False) ->
    (x ∈ fv T -> False).
Proof.
  intros tvars gamma T x H1 H2 H.
  pose proof (defined_FV_IT_var _ _ _ _ H1 H); steps.
Qed.

Hint Resolve defined_FV_IT_var_neg: bfv2.


Lemma defined_FV_context:
  forall tvars x gamma t T A,
    has_type tvars ((x,A) :: gamma) t T ->
    ~(x ∈ fv_context gamma) ->
    subset (fv_context gamma) (support gamma).
Proof.
  repeat step || p_fv || t_sets; eauto 2 with sets.
Qed.

Hint Resolve defined_FV_context: bfv2.

Lemma defined_HT_open:
  forall tvars x gamma t T A k rep,
    has_type tvars ((x,A) :: gamma) (open k t rep) T ->
    ~(x ∈ fv t) ->
    subset (fv t) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_open: bfv2.

Lemma defined_HT_open_type:
  forall tvars x gamma t T A k rep,
    has_type tvars ((x,A) :: gamma) t (open k T rep) ->
    ~(x ∈ fv T) ->
    subset (fv T) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_open_type: bfv2.

Lemma defined_HT_unused:
  forall tvars x gamma t T A,
    has_type tvars ((x,A) :: gamma) t T ->
    ~(x ∈ fv t) ->
    subset (fv t) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_unused: bfv2.

Lemma defined_HT_unused_type:
  forall tvars x gamma t T A,
    has_type tvars ((x,A) :: gamma) t T ->
    ~(x ∈ fv T) ->
    subset (fv T) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_open_type: bfv2.

Lemma defined_HT_context:
  forall tvars x gamma t T ,
    has_type tvars gamma t T ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv_context gamma).
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_HT_context: bfv2.

Lemma defined_IT_context:
  forall tvars x gamma T,
    is_type tvars gamma T ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv_context gamma).
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_IT_context: bfv2.

Lemma defined_IS_context:
  forall tvars x gamma T1 T2 ,
    is_subtype tvars gamma T1 T2 ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv_context gamma).
Proof.
  repeat step || p_sub_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_IS_context: bfv2.

Lemma defined_IS_T1:
  forall tvars x gamma T1 T2 ,
    is_subtype tvars gamma T1 T2 ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv T1).
Proof.
  repeat step || p_sub_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_IS_T1: bfv2.

Lemma defined_IS_T2:
  forall tvars x gamma T1 T2 ,
    is_subtype tvars gamma T1 T2 ->
    ~(x ∈ support gamma) ->
    ~(x ∈ fv T2).
Proof.
  repeat step || p_sub_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_IS_T2: bfv2.
