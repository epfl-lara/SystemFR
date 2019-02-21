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
    subset (pfv t term_var) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open.
Qed.

Hint Resolve defined_FV_HT_1_open: bfv2.

Lemma defined_FV_HT_1_topen:
  forall tvars gamma t T k rep,
    has_type tvars gamma (topen k t rep) T ->
    subset (pfv t term_var) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open.
Qed.

Hint Resolve defined_FV_HT_1_topen: bfv2.

Lemma defined_FV_HT_2_open:
  forall tvars gamma t T k rep,
    has_type tvars gamma t (open k T rep) ->
    subset (pfv T term_var) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open.
Qed.

Hint Resolve defined_FV_HT_2_open: bfv2.

Lemma defined_FV_HT_2_topen:
  forall tvars gamma t T k rep,
    has_type tvars gamma t (topen k T rep) ->
    subset (pfv T term_var) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open.
Qed.

Hint Resolve defined_FV_HT_2_topen: bfv2.

Lemma defined_FV_HT_1_open_3_2:
  forall tvars gamma t T i j x y z X Y Z rep1 rep2,
    ~(x ∈ fv t) ->
    ~(y ∈ fv t) ->
    ~(z ∈ fv t) ->
    has_type tvars
             ((x,X) :: (y,Y) :: (z,Z) :: gamma)
             (open i (open j t rep1) rep2) T ->
    subset (pfv t term_var) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_FV_HT_1_open_3_2: bfv2.

Lemma defined_FV_HT_1_open_4_1:
  forall tvars gamma t T k a b c d A B C D rep,
    ~(a ∈ fv t) ->
    ~(b ∈ fv t) ->
    ~(c ∈ fv t) ->
    ~(d ∈ fv t) ->
    has_type tvars
             ((a,A) :: (b,B) :: (c,C) :: (d,D) :: gamma)
             (open k t rep) T ->
    subset (pfv t term_var) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open; eauto 3 with sets.
Qed.

Hint Resolve defined_FV_HT_1_open_4_1: bfv2.

Lemma defined_FV_HT_1_open_2_1:
  forall tvars gamma t T i x y X Y rep,
    ~(x ∈ fv t) ->
    ~(y ∈ fv t) ->
    has_type tvars
             ((x,X) :: (y,Y) :: gamma)
             (open i t rep) T ->
    subset (pfv t term_var) (support gamma).
Proof.
  repeat step || p_fv || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_FV_HT_1_open_2_1: bfv2.

Lemma defined_FV_HT_1_var:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    x ∈ pfv t term_var ->
    (x ∈ support gamma).
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_FV_HT_1_var: bfv2.

Lemma defined_FV_HT_1_var_neg:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    (x ∈ support gamma -> False) ->
    (x ∈ pfv t term_var -> False).
Proof.
  intros tvars gamma t T x H1 H2 H.
  pose proof (defined_FV_HT_1_var _ _ _ _ _ H1 H); steps.
Qed.

Hint Resolve defined_FV_HT_1_var_neg: bfv2.

Lemma defined_FV_HT_2_var:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    x ∈ pfv T term_var ->
    x ∈ support gamma.
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_FV_HT_2_var: bfv2.

Lemma defined_FV_HT_2_var_neg:
  forall tvars gamma t T x,
    has_type tvars gamma t T ->
    (x ∈ support gamma -> False) ->
    (x ∈ pfv T term_var -> False).
Proof.
  intros tvars gamma t T x H1 H2 H.
  pose proof (defined_FV_HT_2_var _ _ _ _ _ H1 H); steps.
Qed.

Hint Resolve defined_FV_HT_2_var_neg: bfv2.

Lemma defined_FV_IT_var:
  forall tvars gamma T x,
    is_type tvars gamma T ->
    x ∈ pfv T term_var ->
    x ∈ support gamma.
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Hint Resolve defined_FV_IT_var: bfv2.

Lemma defined_FV_IT_var_neg:
  forall tvars gamma T x,
    is_type tvars gamma T ->
    (x ∈ support gamma -> False) ->
    (x ∈ pfv T term_var -> False).
Proof.
  intros tvars gamma T x H1 H2 H.
  pose proof (defined_FV_IT_var _ _ _ _ H1 H); steps.
Qed.

Hint Resolve defined_FV_IT_var_neg: bfv2.


Lemma defined_FV_context:
  forall tvars x gamma t T A,
    has_type tvars ((x,A) :: gamma) t T ->
    ~(x ∈ pfv_context gamma term_var) ->
    subset (pfv_context gamma term_var) (support gamma).
Proof.
  repeat step || p_fv || t_sets; eauto 2 with sets.
Qed.

Hint Resolve defined_FV_context: bfv2.

Lemma defined_HT_open:
  forall tvars x gamma t T A k rep,
    has_type tvars ((x,A) :: gamma) (open k t rep) T ->
    ~(x ∈ pfv t term_var) ->
    subset (pfv t term_var) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_open: bfv2.

Lemma defined_HT_open_type:
  forall tvars x gamma t T A k rep,
    has_type tvars ((x,A) :: gamma) t (open k T rep) ->
    ~(x ∈ pfv T term_var) ->
    subset (pfv T term_var) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_open_type: bfv2.

Lemma defined_HT_unused:
  forall tvars x gamma t T A,
    has_type tvars ((x,A) :: gamma) t T ->
    ~(x ∈ pfv t term_var) ->
    subset (pfv t term_var) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_unused: bfv2.

Lemma defined_HT_unused_type:
  forall tvars x gamma t T A,
    has_type tvars ((x,A) :: gamma) t T ->
    ~(x ∈ pfv T term_var) ->
    subset (pfv T term_var) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_HT_open_type: bfv2.

Lemma defined_HT_context:
  forall tvars x gamma t T ,
    has_type tvars gamma t T ->
    ~(x ∈ support gamma) ->
    ~(x ∈ pfv_context gamma term_var).
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Ltac t_defined_HT_context :=
  match goal with
  | H1: has_type ?tvars ?gamma ?t ?T,
    H2: ?x ∈ support ?gamma -> False,
    H3: ?x ∈ pfv_context ?gamma term_var |- _ =>
    apply False_ind; apply (defined_HT_context tvars x gamma t T H1 H2 H3)
  end.

Hint Extern 1 => t_defined_HT_context: bfv2.

Lemma defined_IT_open:
  forall tvars x gamma T A k rep,
    is_type tvars ((x,A) :: gamma) (open k T rep) ->
    ~(x ∈ pfv T term_var) ->
    subset (pfv T term_var) (support gamma).
Proof.
  repeat step || p_fv || t_sets || t_subset_open; eauto 2 with sets.
Qed.

Hint Resolve defined_IT_open: bfv2.

Lemma defined_IT_context:
  forall tvars x gamma T,
    is_type tvars gamma T ->
    ~(x ∈ support gamma) ->
    ~(x ∈ pfv_context gamma term_var).
Proof.
  repeat step || p_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Ltac t_defined_IT_context :=
  match goal with
  | H1: is_type ?tvars ?gamma ?T,
    H2: ?x ∈ support ?gamma -> False,
    H3: ?x ∈ pfv_context ?gamma term_var |- _ =>
    apply False_ind; apply (defined_IT_context tvars x gamma T H1 H2 H3)
  end.

Hint Extern 1 => t_defined_IT_context: bfv2.

Lemma defined_IS_context:
  forall tvars x gamma T1 T2 ,
    is_subtype tvars gamma T1 T2 ->
    ~(x ∈ support gamma) ->
    ~(x ∈ pfv_context gamma term_var).
Proof.
  repeat step || p_sub_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Ltac t_defined_IS_context :=
  match goal with
  | H1: is_subtype ?tvars ?gamma ?T1 ?T2,
    H2: ?x ∈ support ?gamma -> False,
    H3: ?x ∈ pfv_context ?gamma term_var |- _ =>
    apply False_ind; apply (defined_IS_context tvars x gamma T1 T2 H1 H2 H3)
  end.

Hint Extern 1 => t_defined_IS_context: bfv2.

Lemma defined_IS_T1:
  forall tvars x gamma T1 T2 ,
    is_subtype tvars gamma T1 T2 ->
    ~(x ∈ support gamma) ->
    ~(x ∈ pfv T1 term_var).
Proof.
  repeat step || p_sub_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Ltac t_defined_IS_T1 :=
  match goal with
  | H1: is_subtype ?tvars ?gamma ?T1 ?T2,
    H2: ?x ∈ support ?gamma -> False,
    H3: ?x ∈ pfv ?T1 term_var |- _ =>
    apply False_ind; apply (defined_IS_T1 tvars x gamma T1 T2 H1 H2 H3)
  end.

Hint Extern 1 => t_defined_IS_T1: bfv2.

Lemma defined_IS_T2:
  forall tvars x gamma T1 T2 ,
    is_subtype tvars gamma T1 T2 ->
    ~(x ∈ support gamma) ->
    ~(x ∈ pfv T2 term_var).
Proof.
  repeat step || p_sub_fv || unfold subset in * || instantiate_any || t_listutils.
Qed.

Ltac t_defined_IS_T2 :=
  match goal with
  | H1: is_subtype ?tvars ?gamma ?T1 ?T2,
    H2: ?x ∈ support ?gamma -> False,
    H3: ?x ∈ pfv ?T2 term_var |- _ =>
    apply False_ind; apply (defined_IS_T2 tvars x gamma T1 T2 H1 H2 H3)
  end.

Hint Extern 1 => t_defined_IS_T2: bfv2.
