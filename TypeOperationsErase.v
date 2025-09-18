From Stdlib Require Import String.

Require Export SystemFR.Trees.

Require Export SystemFR.Syntax.


Require Export SystemFR.WFLemmas.
Require Export SystemFR.TWFLemmas.

Require Export SystemFR.FVLemmas.
Require Export SystemFR.AnnotatedTermLemmas.
Require Export SystemFR.Tactics.
Require Export SystemFR.TypeOperations.
Require Export SystemFR.ListUtils.

Require Export SystemFR.TypeErasure.

Lemma ite_type_erase:
  forall b T1 T2 T, T_ite_push b T1 T2 T ->
    T_ite_push (erase_term b) (erase_type T1) (erase_type T2) (erase_type T).
Proof.
  induction 1; repeat step || constructor;
    eauto with fv.
Qed.
