Require Export SystemFR.TWFLemmas.
Require Export SystemFR.ErasedTermLemmas.

Require Import PeanoNat.
Require Import Psatz.

Opaque PeanoNat.Nat.eq_dec.

Fixpoint swap_type_holes t i j :=
  match t with
  | fvar _ _ => t
  | lvar k type_var =>
    if (PeanoNat.Nat.eq_dec k i)
    then lvar j type_var
    else if (PeanoNat.Nat.eq_dec k j)
    then lvar i type_var
    else t
  | lvar k term_var => t

  | notype_err => t
  | err T => err (swap_type_holes T i j)

  | notype_lambda t' => notype_lambda (swap_type_holes t' i j)
  | lambda T t' => lambda (swap_type_holes T i j) (swap_type_holes t' i j)
  | app t1 t2 => app (swap_type_holes t1 i j) (swap_type_holes t2 i j)

  | forall_inst t1 t2 => forall_inst (swap_type_holes t1 i j) (swap_type_holes t2 i j)

  | type_abs t => type_abs (swap_type_holes t (S i) (S j))
  | type_inst t T => type_inst (swap_type_holes t i j) (swap_type_holes T i j)

  | uu => t

  | tsize t => tsize (swap_type_holes t i j)

  | pp t1 t2 => pp (swap_type_holes t1 i j) (swap_type_holes t2 i j)
  | pi1 t => pi1 (swap_type_holes t i j)
  | pi2 t => pi2 (swap_type_holes t i j)

  | because t1 t2 => because (swap_type_holes t1 i j) (swap_type_holes t2 i j)
  | get_refinement_witness t1 t2 => get_refinement_witness (swap_type_holes t1 i j) (swap_type_holes t2 i j)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (swap_type_holes t1 i j) (swap_type_holes t2 i j) (swap_type_holes t3 i j)
  | boolean_recognizer r t => boolean_recognizer r (swap_type_holes t i j)

  | zero => t
  | succ t' => succ (swap_type_holes t' i j)
  | tmatch t' t1 t2 =>
      tmatch
          (swap_type_holes t' i j)
          (swap_type_holes t1 i j)
          (swap_type_holes t2 i j)

  | unary_primitive o t => unary_primitive o (swap_type_holes t i j)
  | binary_primitive o t1 t2 => binary_primitive o (swap_type_holes t1 i j) (swap_type_holes t2 i j)

  | tfix T t' => tfix (swap_type_holes T i j) (swap_type_holes t' i j)
  | notype_tfix t' => notype_tfix (swap_type_holes t' i j)

  | notype_tlet t1 t2 =>
      notype_tlet (swap_type_holes t1 i j) (swap_type_holes t2 i j)
  | tlet t1 T t2 =>
      tlet (swap_type_holes t1 i j) (swap_type_holes T i j) (swap_type_holes t2 i j)

  | trefl t1 t2 => trefl (swap_type_holes t1 i j) (swap_type_holes t2 i j)

  | tfold T t => tfold (swap_type_holes T i j) (swap_type_holes t i j)
  | tunfold t => tunfold (swap_type_holes t i j)
  | tunfold_in t1 t2 => tunfold_in (swap_type_holes t1 i j) (swap_type_holes t2 i j)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (swap_type_holes t1 i j) (swap_type_holes t2 i j)

  | tleft t' => tleft (swap_type_holes t' i j)
  | tright t' => tright (swap_type_holes t' i j)
  | sum_match t' tl tr => sum_match (swap_type_holes t' i j) (swap_type_holes tl i j) (swap_type_holes tr i j)

  | typecheck t T => typecheck (swap_type_holes t i j) (swap_type_holes T i j)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_arrow T1 T2 => T_arrow (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_sum T1 T2 => T_sum (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_refine T p => T_refine (swap_type_holes T i j) (swap_type_holes p i j)
  | T_type_refine T1 T2 => T_type_refine (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_intersection T1 T2 => T_intersection (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_union T1 T2 => T_union (swap_type_holes T1 i j) (swap_type_holes T2 i j)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (swap_type_holes t1 i j) (swap_type_holes t2 i j)
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
  induction t; repeat step || t_equality || rewrite topen_none; eauto with twf lia.
Qed.

Lemma swap_nothing:
  forall T k i j,
    twf T k ->
    k <= i ->
    k <= j ->
    swap_type_holes T i j = T.
Proof.
  induction T; repeat step || t_equality; eauto with lia.
Qed.

Lemma is_erased_swap:
  forall T i j,
    is_erased_type T ->
    is_erased_type (swap_type_holes T i j).
Proof.
  induction T; repeat step || apply_any || rewrite (swap_nothing _ 0);
    eauto with lia twf.
Qed.

#[global]
Hint Resolve is_erased_swap: erased.

Lemma twf_swap:
  forall T k rep,
    twf rep 0 ->
    twf T (S k) ->
    twf (topen (S k) (swap_type_holes T k (S k)) rep) k.
Proof.
  induction T; steps; eauto with twf lia.
Qed.

#[global]
Hint Resolve twf_swap: twf.

Lemma twf_swap2:
  forall T k rep,
    twf rep 0 ->
    twf T (S (S k)) ->
    twf (topen (S k) (swap_type_holes T k (S k)) rep) (S k).
Proof.
  induction T; repeat step || unshelve eauto with twf lia.
Qed.

#[global]
Hint Resolve twf_swap2: twf.

Lemma wf_swap:
  forall T k i j,
    wf T k ->
    wf (swap_type_holes T i j) k.
Proof.
  induction T; steps.
Qed.

#[global]
Hint Resolve wf_swap: wf.

Lemma swap_type_holes_twice:
  forall T i j,
    swap_type_holes (swap_type_holes T i j) i j = T.
Proof.
  induction T; steps.
Qed.

Lemma pfv_swap_type_holes:
  forall T i j tag, pfv (swap_type_holes T i j) tag = pfv T tag.
Proof.
  induction T; steps.
Qed.

#[global]
Hint Extern 1 => rewrite pfv_swap_type_holes: fv.

Lemma topen_swap:
  forall T i j rep,
    twf rep 0 ->
    topen i (swap_type_holes T j i) rep =
    swap_type_holes (topen j T rep) j i.
Proof.
  induction T; repeat step || t_equality || rewrite (swap_nothing _ 0);
    try lia.
Qed.

Lemma topen_swap2:
  forall T k i j rep,
    twf rep 0 ->
    k <> i ->
    k <> j ->
    topen k (swap_type_holes T j i) rep =
    swap_type_holes (topen k T rep) j i.
Proof.
  induction T; repeat step || t_equality || rewrite (swap_nothing _ 0);
    try lia.
Qed.
