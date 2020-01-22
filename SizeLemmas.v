Require Export SystemFR.SwapTypeHoles.
Require Export SystemFR.SwapTermHoles.

Require Import Omega.

(* measure for ensuring termination of reducible_values *)
(* see file ReducibilityMeasure for the full measure *)
Fixpoint type_nodes T: nat :=
  match T with
  | T_unit => 0
  | T_bool => 0
  | T_nat => 0
  | T_refine A p => 1 + type_nodes A
  | T_type_refine A B => 1 + type_nodes A + type_nodes B
  | T_arrow A B => 1 + type_nodes A + type_nodes B
  | T_prod A B => 1 + type_nodes A + type_nodes B
  | T_sum A B => 1 + type_nodes A + type_nodes B
  | T_intersection A B => 1 + type_nodes A + type_nodes B
  | T_union A B => 1 + type_nodes A + type_nodes B
  | T_top => 0
  | T_bot => 0
  | T_equiv _ _ => 0
  | T_forall A B => 1 + type_nodes A + type_nodes B
  | T_exists A B => 1 + type_nodes A + type_nodes B
  | T_abs T => 1 + type_nodes T
  | T_rec _ T0 Ts => 1 + type_nodes T0 + type_nodes Ts

  | _ => 0
  end.

Lemma type_nodes_term:
  forall t,
    is_erased_term t ->
    type_nodes t = 0.
Proof.
  induction t; steps.
Qed.

Lemma type_nodes_opening:
  forall T k rep,
    is_erased_type T ->
    is_erased_term rep ->
    type_nodes (open k T rep) = type_nodes T.
Proof.
  induction T; repeat step || rewrite_any || apply type_nodes_term_form;
    try omega.
Qed.

Hint Rewrite type_nodes_opening: bsize.

Lemma type_nodes_opening_var:
  forall T k X, type_nodes (open k T (fvar X type_var)) = type_nodes T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite type_nodes_opening_var: bsize.

Lemma type_nodes_topening_var:
  forall T k X, type_nodes (topen k T (fvar X type_var)) = type_nodes T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite type_nodes_topening_var: bsize.

Lemma type_nodes_swap_type_holes:
  forall t i j, type_nodes (swap_type_holes t i j) = type_nodes t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite type_nodes_swap_type_holes: bsize.

Lemma type_nodes_swap_term_holes:
  forall t i j, type_nodes (swap_term_holes t i j) = type_nodes t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite type_nodes_swap_term_holes: bsize.
