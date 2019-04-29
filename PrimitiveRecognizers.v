Require Import SystemFR.Trees.

Definition is_pair (v: tree): tree :=
  match v with
  | pp _ _ => ttrue
  | _ => tfalse
  end.

Definition is_succ (v: tree): tree :=
  match v with
  | succ _ => ttrue
  | _ => tfalse
  end.

Definition is_lambda (v: tree): tree :=
  match v with
  | notype_lambda _ => ttrue
  | _ => tfalse
  end.
