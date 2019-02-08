Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TWFLemmas.

Require Import PeanoNat.

Fixpoint swap_type_holes t i j :=
  match t with
  | fvar _ _ => t
  | lvar k type_var =>
    if (Nat.eq_dec k i)
    then lvar j type_var
    else if (Nat.eq_dec k j)
    then lvar i type_var
    else t
  | lvar k term_var => t
  | err => t

  | notype_lambda t' => notype_lambda (swap_type_holes t' i j)
  | lambda T t' => lambda (swap_type_holes T i j) (swap_type_holes t' i j)
  | app t1 t2 => app (swap_type_holes t1 i j) (swap_type_holes t2 i j)

  | type_abs t => type_abs (swap_type_holes t (S i) (S j))
  | type_inst t T => type_inst (swap_type_holes t i j) (swap_type_holes T i j)
  | notype_inst t => notype_inst (swap_type_holes t i j)

  | uu => t

  | pp t1 t2 => pp (swap_type_holes t1 i j) (swap_type_holes t2 i j)
  | pi1 t => pi1 (swap_type_holes t i j)
  | pi2 t => pi2 (swap_type_holes t i j)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (swap_type_holes t1 i j) (swap_type_holes t2 i j) (swap_type_holes t3 i j)

  | zero => t
  | succ t' => succ (swap_type_holes t' i j)
  | notype_rec t' t1 t2 =>
      notype_rec (swap_type_holes t' i j)
                 (swap_type_holes t1 i j)
                 (swap_type_holes t2 i j)
  | rec T t' t1 t2 =>
      rec (swap_type_holes T i j)
          (swap_type_holes t' i j)
          (swap_type_holes t1 i j)
          (swap_type_holes t2 i j)
  | tmatch t' t1 t2 =>
      tmatch
          (swap_type_holes t' i j)
          (swap_type_holes t1 i j)
          (swap_type_holes t2 i j)

  | tfix T t' => tfix (swap_type_holes T i j) (swap_type_holes t' i j)
  | notype_tfix t' => notype_tfix (swap_type_holes t' i j)

  | notype_tlet t1 t2 =>
      notype_tlet (swap_type_holes t1 i j) (swap_type_holes t2 i j)
  | tlet t1 T t2 =>
      tlet (swap_type_holes t1 i j) (swap_type_holes T i j) (swap_type_holes t2 i j)
  | trefl => t

  | tfold t => tfold (swap_type_holes t i j)
  | tunfold t => tunfold (swap_type_holes t i j)

  | tleft t' => tleft (swap_type_holes t' i j)
  | tright t' => tright (swap_type_holes t' i j)
  | sum_match t' tl tr => sum_match (swap_type_holes t' i j) (swap_type_holes tl i j) (swap_type_holes tr i j)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_arrow T1 T2 => T_arrow (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_sum T1 T2 => T_sum (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_refine T p => T_refine (swap_type_holes T i j) (swap_type_holes p i j)
  | T_let t A B => T_let (swap_type_holes t i j) (swap_type_holes A i j) (swap_type_holes B i j)
  | T_singleton t => T_singleton (swap_type_holes t i j)
  | T_intersection T1 T2 => T_intersection (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_union T1 T2 => T_union (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (swap_type_holes t1 i j) (swap_type_holes t2 i j)
  | T_forall T1 T2 => T_forall (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_exists T1 T2 => T_exists (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_abs T => T_abs (swap_type_holes T (S i) (S j))
  | T_rec n T0 Ts => T_rec (swap_type_holes n i j) (swap_type_holes T0 i j) (swap_type_holes Ts (S i) (S j))
  end.

Lemma open_swap:
  (forall t j1 j2 rep1 rep2,
    j1 <> j2 ->
    twf rep1 0 ->
    twf rep2 0 ->
    topen j1 (topen j2 t rep2) rep1 =
    topen j1 (topen j2 (swap_type_holes t j1 j2) rep1) rep2).
Proof.
  induction t; repeat step || tequality || rewrite topen_none; eauto with btwf omega.
Qed.
