Require Import Termination.Tactics.
Require Import Termination.Syntax.

Fixpoint term_form t :=
  match t with
  | fvar y term_var => True
  | fvar y type_var => False
  | lvar i => True
  | err => True

  | uu => True

  | lambda T t' => True
  | app t1 t2 => True

  | pp t1 t2 => True
  | pi1 t => True
  | pi2 t => True

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => True

  | zero => True
  | succ t' => True
  | rec T t' t1 t2 => True
  | tmatch t' t1 t2 => True

  | tlet _ _ _ => True
  | trefl => True

  | T_unit => False
  | T_bool => False
  | T_nat => False
  | T_prod T1 T2 => False
  | T_arrow T1 T2 => False
  | T_refine T p => False
  | T_let t A B => False
  | T_singleton t => False
  | T_intersection T1 T2 => False
  | T_union T1 T2 => False
  | T_top => False
  | T_bot => False
  | T_equal t1 t2 => False
  | T_forall T1 T2 => False
  | T_exists T1 T2 => False
  end.
