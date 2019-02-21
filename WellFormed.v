Require Import Equations.Equations.

Require Import Coq.Lists.List.

Require Import PeanoNat.

Require Import Termination.Trees.
Require Import Termination.Tactics.

Fixpoint wf t k :=
  match t with
  | fvar _ _ => True
  | lvar i term_var => i < k
  | lvar i type_var => True

  | notype_err => True
  | err T => wf T k

  | uu => True

  | tsize t => wf t k

  | notype_lambda t' => wf t' (S k)
  | lambda T t' => wf T k /\ wf t' (S k)
  | app t1 t2 => wf t1 k /\ wf t2 k

  | forall_inst t1 t2 => wf t1 k /\ wf t2 k

  | type_abs t => wf t k
  | type_inst t T => wf t k /\ wf T k
  | notype_inst t => wf t k

  | pp t1 t2 => wf t1 k /\ wf t2 k
  | pi1 t => wf t k
  | pi2 t => wf t k

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => wf t1 k /\ wf t2 k /\ wf t3 k

  | zero => True
  | succ t' => wf t' k
  | notype_rec t' t1 t2 =>
      wf t' k /\
      wf t1 k /\
      wf t2 (S (S k))
  | rec T t' t1 t2 =>
      wf T (S k) /\
      wf t' k /\
      wf t1 k /\
      wf t2 (S (S k))
  | tmatch t' t1 t2 =>
      wf t' k /\
      wf t1 k /\
      wf t2 (S k)

  | tfix T t' => wf T (S k) /\ wf t' (S (S k))
  | notype_tfix t' => wf t' (S (S k))

  | notype_tlet t1 t2 => wf t1 k /\ wf t2 (S k)
  | tlet t1 T t2 => wf t1 k /\ wf T k /\ wf t2 (S k)

  | notype_trefl => True
  | trefl t1 t2 => wf t1 k /\ wf t2 k

  | tfold T t' => wf T k /\ wf t' k
  | notype_tfold t' => wf t' k
  | tunfold t' => wf t' k
  | tunfold_in t1 t2 => wf t1 k /\ wf t2 (S k)

  | tleft t' => wf t' k
  | tright t' => wf t' k
  | sum_match t' tl tr => wf t' k /\ wf tl (S k) /\ wf tr (S k)

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_arrow T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_sum T1 T2 => wf T1 k /\ wf T2 k
  | T_refine T p => wf T k /\ wf p (S k)
  | T_let t A B => wf t k /\ wf A k /\ wf B (S k)
  | T_singleton t => wf t k
  | T_intersection T1 T2 => wf T1 k /\ wf T2 k
  | T_union T1 T2 => wf T1 k /\ wf T2 k
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => wf t1 k /\ wf t2 k
  | T_forall T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_exists T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_abs T => wf T k
  | T_rec n T0 Ts => wf n k /\ wf T0 k /\ wf Ts k
  end.

Fixpoint twf t k :=
  match t with
  | fvar _ _ => True
  | lvar i type_var => i < k
  | lvar i term_var => True

  | err T => twf T k
  | notype_err => True

  | uu => True

  | tsize t => twf t k

  | notype_lambda t' => twf t' k
  | lambda T t' => twf T k /\ twf t' k
  | app t1 t2 => twf t1 k /\ twf t2 k

  | forall_inst t1 t2 => twf t1 k /\ twf t2 k

  | type_abs t => twf t (S k)
  | type_inst t T => twf t k /\ twf T k
  | notype_inst t => twf t k

  | pp t1 t2 => twf t1 k /\ twf t2 k
  | pi1 t => twf t k
  | pi2 t => twf t k

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => twf t1 k /\ twf t2 k /\ twf t3 k

  | zero => True
  | succ t' => twf t' k
  | notype_rec t' t1 t2 =>
      twf t' k /\
      twf t1 k /\
      twf t2 k
  | rec T t' t1 t2 =>
      twf T k /\
      twf t' k /\
      twf t1 k /\
      twf t2 k
  | tmatch t' t1 t2 =>
      twf t' k /\
      twf t1 k /\
      twf t2 k

  | tfix T t' => twf T k /\ twf t' k
  | notype_tfix t' => twf t' k

  | notype_tlet t1 t2 => twf t1 k /\ twf t2 k
  | tlet t1 T t2 => twf t1 k /\ twf T k /\ twf t2 k

  | notype_trefl => True
  | trefl t1 t2 => twf t1 k /\ twf t2 k

  | notype_tfold t => twf t k
  | tfold T t => twf T k /\ twf t k
  | tunfold t => twf t k
  | tunfold_in t1 t2 => twf t1 k /\ twf t2 k

  | tleft t => twf t k
  | tright t => twf t k
  | sum_match t' tl tr => twf t' k /\ twf tl k /\ twf tr k

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => twf T1 k /\ twf T2 k
  | T_arrow T1 T2 => twf T1 k /\ twf T2 k
  | T_sum T1 T2 => twf T1 k /\ twf T2 k
  | T_refine T p => twf T k /\ twf p k
  | T_let t A B => twf t k /\ twf A k /\ twf B k
  | T_singleton t => twf t k
  | T_intersection T1 T2 => twf T1 k /\ twf T2 k
  | T_union T1 T2 => twf T1 k /\ twf T2 k
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => twf t1 k /\ twf t2 k
  | T_forall T1 T2 => twf T1 k /\ twf T2 k
  | T_exists T1 T2 => twf T1 k /\ twf T2 k
  | T_abs T => twf T (S k)
  | T_rec n T0 Ts => twf n k /\ twf T0 k /\ twf Ts (S k)
  end.

Fixpoint wfs (gamma: list (nat * tree)) k :=
  match gamma with
  | nil => True
  | (x,A) :: gamma' => wf A k /\ wfs gamma' k
  end.

Fixpoint twfs (gamma: list (nat * tree)) k :=
  match gamma with
  | nil => True
  | (x,A) :: gamma' => twf A k /\ twfs gamma' k
  end.
