Require Import Termination.Syntax.
Require Import Termination.Equivalence.
Require Import Termination.Tactics.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.


Open Scope list_scope.


Lemma subst_types_equivalent_true:
  forall t l1 l2,
    equivalent (psubstitute t l1 type_var) ttrue ->
    equivalent (psubstitute t l2 type_var) ttrue.
Proof.
Admitted.

Hint Resolve subst_types_equivalent_true: bparam.

Lemma subst_types_equivalent_false:
  forall t l1 l2,
    equivalent (psubstitute t l1 type_var) tfalse ->
    equivalent (psubstitute t l2 type_var) tfalse.
Proof.
Admitted.

Hint Resolve subst_types_equivalent_false: bparam.
