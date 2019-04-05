Require Import Coq.Strings.String.
Require Import Omega.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.Sets.
Require Import SystemFR.ListUtils.
Require Import SystemFR.WFLemmas.
Require Import SystemFR.TWFLemmas.


Open Scope string_scope.
Open Scope list_scope.

Lemma open_topen:
  forall t k1 k2 rep1 rep2,
    wf rep2 0 ->
    twf rep1 0 ->
    open k1 (topen k2 t rep2) rep1 = topen k2 (open k1 t rep1) rep2.
Proof.
  induction t;
    repeat step || tequality || apply_any ||
      (rewrite topen_none by (steps;eauto with btwf omega)) ||
      (rewrite open_none by (steps;eauto with bwf omega));
        eauto with bwf btwf omega.
Qed.
