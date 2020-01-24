Require Import Coq.Strings.String.
Require Import Omega.

Require Export SystemFR.Syntax.
Require Export SystemFR.Tactics.
Require Export SystemFR.AssocList.

Require Export SystemFR.ListUtils.

Require Export SystemFR.WFLemmas.

Open Scope string_scope.
Open Scope list_scope.

Lemma wf_close:
  forall t k x,
    wf t k ->
    wf (close k t x) (S k).
Proof.
  induction t; steps.
Qed.

Lemma wf_tclose:
  forall t i j x,
    wf t i ->
    wf (tclose j t x) i.
Proof.
  induction t; steps.
Qed.

Lemma twf_tclose:
  forall T k X,
    twf T k ->
    twf (tclose k T X) (S k).
Proof.
  induction T; steps.
Qed.

Lemma twf_close:
  forall t i j x,
    twf t i ->
    twf (close j t x) i.
Proof.
  induction t; steps.
Qed.

Hint Resolve wf_close: wf.
Hint Resolve twf_tclose: twf.
Hint Resolve wf_tclose: wf.
Hint Resolve twf_close: twf.
