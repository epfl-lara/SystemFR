Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.FVLemmas.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.TermList.

Lemma satisfies_closed_mapping:
  forall P lterms gamma tag,
    satisfies P gamma lterms ->
    pclosed_mapping lterms tag.
Proof.
  induction lterms; destruct tag;
    repeat step || step_inversion satisfies ||
           unfold closed_term in *; eauto.
Qed.

Hint Extern 50 => solve [ eapply satisfies_closed_mapping; eassumption ]: fv.

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

Hint Extern 50 => solve [ eapply closed_mapping_append1; eauto 1 ]: b_cmap.
Hint Extern 50 => solve [ eapply closed_mapping_append2; eauto 1 ]: b_cmap.

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

Hint Extern 50 => eapply satisfies_fv_nil: fv.

Lemma fv_satisfies_nil:
  forall P gamma lterms t,
    satisfies P gamma lterms ->
    subset (fv t) (support gamma) ->
    fv (substitute t lterms) = nil.
Proof.
  repeat step || t_termlist || list_utils || apply fv_nils2 || rewrite_any;
    eauto with fv b_cmap.
Qed.

Hint Extern 50 => eapply fv_satisfies_nil: fv.

Lemma subset_same_support:
  forall P gamma lterms S,
    satisfies P gamma lterms ->
    subset S (support gamma) ->
    subset S (support lterms).
Proof.
  repeat step || t_termlist || rewrite_any.
Qed.

Hint Immediate subset_same_support: fv.

Lemma fv_nils3:
  forall P gamma t l,
    is_annotated_term t ->
    subset (pfv t term_var) (support gamma) ->
    satisfies P (erase_context gamma) l ->
    pfv (psubstitute (erase_term t) l term_var) term_var = nil.
Proof.
  intros.
  apply fv_nils2; eauto with fv.
  eapply subset_same_support; eauto;
    repeat step || t_subset_erase || rewrite erased_context_support.
Qed.

Hint Immediate fv_nils3: fv.

Lemma fv_subst_different_tag:
  forall t l tag tag',
    pclosed_mapping l tag ->
    tag <> tag' ->
    pfv (psubstitute t l tag') tag = pfv t tag.
Proof.
  induction t; repeat step || f_equal; eauto with fv.
Qed.

Lemma pfv_in_subst:
  forall (T : tree) (l : list (nat * tree)) (tag1 tag2 : fv_tag) (X : nat),
    pclosed_mapping l tag1 ->
    X ∈ pfv (psubstitute T l tag2) tag1->
    X ∈ pfv T tag1.
Proof.
  destruct tag1, tag2; repeat step || rewrite fv_subst_different_tag in * by steps.
  - epose proof (fv_subst2 _ _ _ X H0);
    repeat step || list_utils;
    eauto using closed_mapping_fv with exfalso.
  - epose proof (fv_subst2 _ _ _ X H0);
    repeat step || list_utils;
    eauto using closed_mapping_fv with exfalso.
Qed.

Ltac t_pfv_in_subst :=
  match goal with
  | H: _ ∈ pfv (psubstitute _ _ _) _ |- _ =>
      poseNew (Mark H "pfv_in_subst");
      unshelve epose proof (pfv_in_subst _ _ _ _ _ _ H)
  end.
