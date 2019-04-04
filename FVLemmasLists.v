
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.TermProperties.
Require Import SystemFR.Sets.
Require Import SystemFR.AssocList.
Require Import SystemFR.FVLemmas.
Require Import SystemFR.TermList.
Require Import SystemFR.ListUtils.

Lemma satisfies_closed_mapping:
  forall P lterms gamma tag,
    satisfies P gamma lterms ->
    pclosed_mapping lterms tag.
Proof.
  induction lterms; destruct tag;
    repeat step || step_inversion satisfies ||
           unfold closed_term in *; eauto.
Qed.

Hint Extern 50 => eapply satisfies_closed_mapping: bfv.

Lemma closed_mapping_append1:
  forall l1 l2 tag,
    pclosed_mapping (l1 ++ l2) tag ->
    pclosed_mapping l1 tag.
Proof.
  induction l1; steps; eauto.
Qed.

Lemma closed_mapping_append2:
  forall l1 l2 tag,
    pclosed_mapping (l1 ++ l2) tag ->
    pclosed_mapping l2 tag.
Proof.
  induction l1; steps.
Qed.

Hint Extern 50 => eapply closed_mapping_append1: b_cmap.
Hint Extern 50 => eapply closed_mapping_append2: b_cmap.

Lemma closed_mapping_append:
  forall l1 l2 tag,
    pclosed_mapping l1 tag ->
    pclosed_mapping l2 tag ->
    pclosed_mapping (l1 ++ l2) tag.
Proof.
  induction l1; steps.
Qed.

Hint Extern 50 => eapply closed_mapping_append: b_cmap.

Lemma satisfies_fv_nil:
  forall P gamma lterms,
    satisfies P gamma lterms ->
    forall t,
      t ∈ range lterms ->
      fv t = nil.
Proof.
  steps.
  eapply closed_mapping_range; eauto.
  eapply satisfies_closed_mapping; eauto.
Qed.

Hint Extern 50 => eapply satisfies_fv_nil: bfv.

Lemma fv_satisfies_nil:
  forall P gamma lterms t,
    satisfies P gamma lterms ->
    subset (fv t) (support gamma) ->
    fv (substitute t lterms) = nil.
Proof.
  repeat step || t_termlist || t_listutils || apply fv_nils2 || rewrite_any;
    eauto with bfv b_cmap.
Qed.

Hint Extern 50 => eapply fv_satisfies_nil: bfv.

Lemma fv_subst_different_tag:
  forall t l tag tag',
    pclosed_mapping l tag ->
    tag <> tag' ->
    pfv (psubstitute t l tag') tag = pfv t tag.
Proof.
  induction t; repeat step || f_equal; eauto with bfv.
Qed.

Lemma pfv_in_subst:
  forall (T : tree) (l : list (nat * tree)) (tag1 tag2 : fv_tag) (X : nat),
    pclosed_mapping l tag1 ->
    X ∈ pfv (psubstitute T l tag2) tag1->
    X ∈ pfv T tag1.
Proof.
  destruct tag1, tag2; repeat step || rewrite fv_subst_different_tag in * by steps.
  - epose proof (fv_subst2 _ _ _ X H0);
    repeat step || t_listutils;
    eauto using closed_mapping_fv with falsity.
  - epose proof (fv_subst2 _ _ _ X H0);
    repeat step || t_listutils;
    eauto using closed_mapping_fv with falsity.
Qed.

Ltac t_pfv_in_subst :=
  match goal with
  | H: _ ∈ pfv (psubstitute _ _ term_var) type_var |- _ =>
      poseNew (Mark H "pfv_in_subst");
      unshelve epose proof (pfv_in_subst _ _ _ _ _ _ H)
  | H: _ ∈ pfv (psubstitute _ _ type_var) term_var |- _ =>
      poseNew (Mark H "pfv_in_subst");
      unshelve epose proof (pfv_in_subst _ _ _ _ _ _ H)
  end.
