Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Tactics.

(* always 0 for non-values *)
Fixpoint tsize_semantics t: nat :=
  match t with
  | fvar _ _ => 0
  | lvar _ _ => 0
  | err => 0

  | uu => 0

  | tsize t => 0

  | notype_lambda t' => 0
  | lambda T t' => 0
  | app t1 t2 => 0

  | pp t1 t2 => 1 + tsize_semantics t1 + tsize_semantics t2
  | pi1 t' => 0
  | pi2 t' => 0

  | ttrue => 0
  | tfalse => 0
  | ite t1 t2 t3 => 0

  | zero => 0
  | succ t' =>  1 + tsize_semantics t'
  | notype_rec t' t0 ts => 0
  | rec T t' t0 ts => 0
  | tmatch t' t0 ts => 0

  | tfix T t' => 0
  | notype_tfix t' => 0

  | notype_tlet t1 t2 => 0
  | tlet t1 A t2 => 0
  | trefl => 0

  | type_abs t => 0
  | type_inst t T => 0
  | notype_inst t => 0

  | tfold t => 1 + tsize_semantics t
  | tunfold t => 0

  | tright t => 1 + tsize_semantics t
  | tleft t => 1 + tsize_semantics t
  | sum_match t tl tr => 0

  | T => 0
  end.
