Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SwapHoles.

Require Import Omega.

(* measure for ensuring termination of reducible_values *)
(* see file ReducibilityMeasure for the full measure *)
Fixpoint size T: nat :=
  match T with
  | T_unit => 0
  | T_bool => 0
  | T_nat => 0
  | T_refine A p => 1 + size A
  | T_type_refine A B => 1 + size A + size B
  | T_arrow A B => 3 + size A + size B
  | T_prod A B => 3 + size A + size B
  | T_sum A B => 1 + size A + size B
  | T_let t B => 2 + size B
  | T_singleton t => 0
  | T_intersection A B => 1 + size A + size B
  | T_union A B => 1 + size A + size B
  | T_top => 0
  | T_bot => 0
  | T_equal _ _ => 0
  | T_forall A B => 3 + size A + size B
  | T_exists A B => 3 + size A + size B
  | T_abs T => 3 + size T
  | T_rec _ T0 Ts => 2 + size T0 + size Ts

  | _ => 0
  end.

Lemma size_term_form:
  forall t, is_erased_term t -> size t = 0.
Proof.
  destruct t; steps.
Qed.

Lemma size_opening:
  forall T k rep, is_erased_term rep -> size (open k T rep) = size T.
Proof.
  induction T; repeat step || rewrite_any || apply size_term_form;
    try omega.
Qed.

Hint Rewrite size_opening: bsize.

Lemma size_opening_var:
  forall T k X, size (open k T (fvar X type_var)) = size T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite size_opening_var: bsize.

Lemma size_topening_var:
  forall T k X, size (topen k T (fvar X type_var)) = size T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite size_topening_var: bsize.

Lemma size_swap:
  forall t i j, size (swap_type_holes t i j) = size t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite size_swap: bsize.
