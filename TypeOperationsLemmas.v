Require Import Coq.Strings.String.

Require Import SystemFR.Trees.
Require Import SystemFR.Sets.
Require Import SystemFR.Syntax.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.TWFLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.AnnotatedTermLemmas.
Require Import SystemFR.Tactics.
Require Import SystemFR.TypeOperations.
Require Import SystemFR.ListUtils.

Lemma ite_type_open:
  forall b T1 T2 T, T_ite b T1 T2 T -> forall k a,
    is_erased_term a ->
    wf b 0 ->
    T_ite b (open k T1 a) (open k T2 a) (open k T a).
Proof.
  induction 1; repeat step || constructor || t_fv_open || t_listutils ||
                      rewrite (open_none b) in * by (eauto with bwf omega) ||
                      rewrite is_erased_term_tfv in * by assumption;
    eauto with bfv.
Qed.

Lemma ite_type_topen:
  forall b T1 T2 T, T_ite b T1 T2 T -> forall k X,
    twf b 0 ->
    T_ite b (topen k T1 (fvar X type_var)) (topen k T2 (fvar X type_var)) (topen k T (fvar X type_var)).
Proof.
  induction 1; repeat step || constructor || t_fv_open || t_listutils ||
                      rewrite (topen_none b) in * by (eauto with btwf omega) ||
                      rewrite is_erased_term_tfv in * by assumption;
    eauto with bfv.
Qed.

Lemma ite_type_subst:
  forall b T1 T2 T, T_ite b T1 T2 T -> forall l,
    T_ite (psubstitute b l term_var) (psubstitute T1 l term_var) (psubstitute T2 l term_var) (psubstitute T l term_var).
Proof.
  induction 1; repeat step || constructor.
Qed.
