Require Import Coq.Strings.String.
Require Import Omega.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.ListUtils.
Require Import Termination.WFLemmas.
Require Import Termination.TWFLemmas.

Open Scope string_scope.
Open Scope list_scope.

Lemma open_topen:
  forall t k1 k2 rep1 rep2,
    twf rep1 0 ->
    wf t 0 ->
    open k1 (topen k2 t rep2) rep1 = topen k2 t (open k1 rep2 rep1).
Proof.
  induction t;
    repeat step || tequality || apply_any ||
      (rewrite topen_none by (steps;eauto with btwf omega));
        eauto with bwf btwf omega.
Admitted.
