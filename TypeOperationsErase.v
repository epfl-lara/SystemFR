Require Import Coq.Strings.String.

Require Import Termination.Trees.
Require Import Termination.Sets.
Require Import Termination.Syntax.

Require Import Termination.WellFormed.
Require Import Termination.WFLemmas.
Require Import Termination.TWFLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.AnnotatedTermLemmas.
Require Import Termination.Tactics.
Require Import Termination.TypeOperations.
Require Import Termination.ListUtils.

Require Import Termination.TypeErasure.

Lemma ite_type_erase:
  forall b T1 T2 T, T_ite b T1 T2 T ->
    T_ite (erase_term b) (erase_type T1) (erase_type T2) (erase_type T).
Proof.
  induction 1; repeat step || constructor;
    eauto with bfv.
Qed.
