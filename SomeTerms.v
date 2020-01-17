Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.

Definition spositive (a: tree): tree :=
  tmatch a tfalse ttrue.

Definition tpred (a: tree): tree :=
  tmatch a (err T_nat) (lvar 0 term_var).

Definition notype_tpred (a: tree): tree :=
  tmatch a notype_err (lvar 0 term_var).

Definition negate (t: tree): tree := ite t tfalse ttrue.
Definition unfold_left (t: tree): tree := sum_match t (lvar 0 term_var) notype_err.
Definition unfold_right (t: tree): tree := sum_match t notype_err (lvar 0 term_var).
