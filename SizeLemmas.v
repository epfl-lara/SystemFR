Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SwapHoles.

Require Import Omega.

(* measure for ensuring termination of reducible_values *)
(* see file ReducibilityMeasure for the full measure *)
Fixpoint typeNodes T: nat :=
  match T with
  | T_unit => 0
  | T_bool => 0
  | T_nat => 0
  | T_refine A p => 1 + typeNodes A
  | T_type_refine A B => 1 + typeNodes A + typeNodes B
  | T_arrow A B => 1 + typeNodes A + typeNodes B
  | T_prod A B => 1 + typeNodes A + typeNodes B
  | T_sum A B => 1 + typeNodes A + typeNodes B
  | T_let t B => 1 + typeNodes B
  | T_singleton t => 0
  | T_intersection A B => 1 + typeNodes A + typeNodes B
  | T_union A B => 1 + typeNodes A + typeNodes B
  | T_top => 0
  | T_bot => 0
  | T_equal _ _ => 0
  | T_forall A B => 1 + typeNodes A + typeNodes B
  | T_exists A B => 1 + typeNodes A + typeNodes B
  | T_abs T => 1 + typeNodes T
  | T_rec _ T0 Ts => 1 + typeNodes T0 + typeNodes Ts

  | _ => 0
  end.

Lemma typeNodes_term_form:
  forall t, is_erased_term t -> typeNodes t = 0.
Proof.
  destruct t; steps.
Qed.

Lemma typeNodes_opening:
  forall T k rep, is_erased_term rep -> typeNodes (open k T rep) = typeNodes T.
Proof.
  induction T; repeat step || rewrite_any || apply typeNodes_term_form;
    try omega.
Qed.

Hint Rewrite typeNodes_opening: bsize.

Lemma typeNodes_opening_var:
  forall T k X, typeNodes (open k T (fvar X type_var)) = typeNodes T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite typeNodes_opening_var: bsize.

Lemma typeNodes_topening_var:
  forall T k X, typeNodes (topen k T (fvar X type_var)) = typeNodes T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite typeNodes_topening_var: bsize.

Lemma typeNodes_swap:
  forall t i j, typeNodes (swap_type_holes t i j) = typeNodes t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite typeNodes_swap: bsize.
