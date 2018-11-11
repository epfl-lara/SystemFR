
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.FVLemmas.
Require Import Termination.TermList.
Require Import Termination.TypeList.
Require Import Termination.ListUtils.

Lemma satisfies_closed_mapping:
  forall P lterms gamma,
    satisfies P gamma lterms ->
    pclosed_mapping lterms term_var.
Proof.
  induction lterms;
    repeat step || step_inversion satisfies ||
           unfold closed_term in * || destruct tag; eauto.
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

Lemma closed_fvs:
  forall l,
    closed_terms l ->
    pclosed_mapping l term_var.
Proof.
  induction l; repeat step || unfold closed_term in * || destruct tag.
Qed.

Hint Extern 50 => eapply closed_fvs: b_cmap.

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

Lemma fv2_nil:
  forall (gamma : M nat term) (t : term) P lterms ltypes,
    subset (pfv t term_var) (support gamma) ->
    closed_terms ltypes ->
    satisfies P gamma lterms ->
    pfv (psubstitute (psubstitute t lterms term_var) ltypes type_var) term_var = nil.
Proof.
  intros; rewrite fv_subst_different_tag; steps; eauto with b_cmap; eauto with bfv.
Qed.

Hint Resolve fv2_nil: bfv.

(*
Lemma fv2_nil2:
  forall (gamma : M nat term) (t2 : term) P (theta: M nat (term -> Prop)) lterms ltypes,
    subset (pfv t2 type_var) (support theta) ->
    closed_terms ltypes ->
    satisfies P gamma lterms ->
    support theta = support ltypes ->
    pfv (psubstitute (psubstitute t2 lterms term_var) ltypes type_var) type_var = nil.
Proof.
  repeat step || apply fv_nils2 || rewrite fv_subst_different_tag;
    eauto with b_cmap sets bfv.
Qed.

Hint Resolve fv2_nil2: bfv.
*)