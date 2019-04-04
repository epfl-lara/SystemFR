Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.

Definition spositive (a: tree): tree :=
  tmatch a tfalse ttrue.

Definition tpred (a: tree): tree :=
  tmatch a (err T_nat) (lvar 0 term_var).

Definition notype_tpred (a: tree): tree :=
  tmatch a notype_err (lvar 0 term_var).
