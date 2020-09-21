Require Import Coq.Strings.String.

Require Export SystemFR.Trees.

Require Export SystemFR.Syntax.


Require Export SystemFR.WFLemmas.
Require Export SystemFR.TWFLemmas.

Require Export SystemFR.FVLemmas.
Require Export SystemFR.AnnotatedTermLemmas.
Require Export SystemFR.Tactics.
Require Export SystemFR.TypeOperations.
Require Export SystemFR.ListUtils.

Lemma ite_type_open:
  forall b T1 T2 T, T_ite_push b T1 T2 T -> forall k a,
    is_erased_term a ->
    wf b 0 ->
    T_ite_push b (open k T1 a) (open k T2 a) (open k T a).
Proof.
  induction 1; repeat step || constructor || fv_open || list_utils ||
                      rewrite (open_none b) in * by (eauto with wf lia) ||
                      rewrite is_erased_term_tfv in * by assumption;
    eauto with fv.
Qed.

Lemma ite_type_topen:
  forall b T1 T2 T, T_ite_push b T1 T2 T -> forall k X,
    twf b 0 ->
    T_ite_push b (topen k T1 (fvar X type_var)) (topen k T2 (fvar X type_var)) (topen k T (fvar X type_var)).
Proof.
  induction 1; repeat step || constructor || fv_open || list_utils ||
                      rewrite (topen_none b) in * by (eauto with twf lia) ||
                      rewrite is_erased_term_tfv in * by assumption;
    eauto with fv.
Qed.

Lemma ite_type_subst:
  forall b T1 T2 T, T_ite_push b T1 T2 T -> forall l,
    T_ite_push (psubstitute b l term_var) (psubstitute T1 l term_var) (psubstitute T2 l term_var) (psubstitute T l term_var).
Proof.
  induction 1; repeat step || constructor.
Qed.
