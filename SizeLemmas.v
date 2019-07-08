Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.SwapHoles.

Require Import Omega.

(* measure for ensuring termination of reducible_values *)
(* see file ReducibilityMeasure for the full measure *)
Fixpoint typeNodes T: nat :=
  match T with
  | ite b T1 T2 => 1 + typeNodes T1 + typeNodes T2

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
  | T_interpret T => 1 + typeNodes T

  | _ => 0
  end.

(*
Lemma typeNodes_term_form:
  forall t, is_erased_term t -> typeNodes t = 0.
Proof.
  destruct t; steps.
Qed.
*)

Lemma typeNodes_opening:
  forall T k rep,
    is_erased_type T ->
    is_erased_term rep ->
    typeNodes (open k T rep) = typeNodes T.
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

Fixpoint count_interpret (t: tree): nat :=
  match t with
  | ite b T1 T2 => count_interpret T1 + count_interpret T2

  | T_refine A p => count_interpret A
  | T_type_refine A B => count_interpret A + count_interpret B
  | T_prod A B => count_interpret A + count_interpret B
  | T_arrow A B => count_interpret A + count_interpret B
  | T_sum A B => count_interpret A + count_interpret B
  | T_let t B => count_interpret B
  | T_intersection A B => count_interpret A + count_interpret B
  | T_union A B => count_interpret A + count_interpret B
  | T_forall A B => count_interpret A + count_interpret B
  | T_exists A B => count_interpret A + count_interpret B
  | T_abs T => count_interpret T
  | T_rec n T0 Ts => count_interpret T0 + count_interpret Ts
  | T_interpret t => 1 + count_interpret t
  | _ => 0
  end.

(*
Lemma count_interpret_term:
  forall t, is_erased_term t -> count_interpret t = 0.
Proof.
  destruct t; steps.
Qed.
*)

Lemma count_interpret_open:
  forall T k rep,
    is_erased_type T ->
    is_erased_term rep ->
    count_interpret (open k T rep) = count_interpret T.
Proof.
  induction T; repeat step || rewrite_any; try omega.
Qed.

Hint Rewrite count_interpret_open: bsize.

Lemma count_interpret_open_var:
  forall T k X, count_interpret (open k T (fvar X type_var)) = count_interpret T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite count_interpret_open_var: bsize.

Lemma count_interpret_topen_var:
  forall T k X, count_interpret (topen k T (fvar X type_var)) = count_interpret T.
Proof.
  induction T; steps.
Qed.

Hint Rewrite count_interpret_topen_var: bsize.

Lemma count_interpret_swap:
  forall t i j, count_interpret (swap_type_holes t i j) = count_interpret t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite count_interpret_swap: bsize.
