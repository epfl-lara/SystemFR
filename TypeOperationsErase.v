Require Import Coq.Strings.String.

Require Import SystemFR.Trees.
Require Import SystemFR.Sets.
Require Import SystemFR.Syntax.

Require Import SystemFR.WellFormed.
Require Import SystemFR.WFLemmas.
Require Import SystemFR.TWFLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.AnnotatedTermLemmas.
Require Import SystemFR.Tactics.
Require Import SystemFR.TypeOperations.
Require Import SystemFR.ListUtils.

Require Import SystemFR.TypeErasure.

Lemma ite_type_erase:
  forall b T1 T2 T, T_ite b T1 T2 T ->
    T_ite (erase_term b) (erase_type T1) (erase_type T2) (erase_type T).
Proof.
  induction 1; repeat step || constructor;
    eauto with bfv.
Qed.
