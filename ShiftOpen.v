Require Import PeanoNat.

Require Export SystemFR.WFLemmas.
Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.TypeErasure.

Opaque Compare_dec.ge_dec.
Opaque Nat.eq_dec.

Fixpoint shift (k: nat) (t: tree) (i: nat) :=
  match t with
  | fvar _ _ => t
  | lvar j term_var => if (Compare_dec.ge_dec j k) then lvar (j + i) term_var else t
  | lvar _ type_var => t
  | notype_err => t
  | err T => err (shift k T i)

  | notype_lambda t' => notype_lambda (shift (S k) t' i)
  | lambda T t' => lambda (shift k T i) (shift (S k) t' i)
  | app t1 t2 => app (shift k t1 i) (shift k t2 i)

  | forall_inst t1 t2 => forall_inst (shift k t1 i) (shift k t2 i)

  | type_abs t => type_abs (shift k t i)
  | type_inst t T => type_inst (shift k t i) (shift k T i)

  | uu => t

  | tsize t => tsize (shift k t i)

  | pp t1 t2 => pp (shift k t1 i) (shift k t2 i)
  | pi1 t => pi1 (shift k t i)
  | pi2 t => pi2 (shift k t i)

  | because t1 t2 => because (shift k t1 i) (shift k t2 i)
  | get_refinement_witness t1 t2 => get_refinement_witness (shift k t1 i) (shift (S k) t2 i)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (shift k t1 i) (shift k t2 i) (shift k t3 i)
  | boolean_recognizer r t => boolean_recognizer r (shift k t i)

  | zero => t
  | succ t' => succ (shift k t' i)
  | tmatch t' t1 t2 =>
      tmatch
          (shift k t' i)
          (shift k t1 i)
          (shift (S k) t2 i)

  | unary_primitive o t => unary_primitive o (shift k t i)
  | binary_primitive o t1 t2 => binary_primitive o (shift k t1 i) (shift k t2 i)

  | tfix T t' => tfix (shift (S k) T i) (shift (S (S k)) t' i)
  | notype_tfix t' => notype_tfix (shift (S (S k)) t' i)

  | notype_tlet t1 t2 =>
      notype_tlet (shift k t1 i) (shift (S k) t2 i)
  | tlet t1 T t2 =>
      tlet (shift k t1 i) (shift k T i) (shift (S k) t2 i)
  | trefl t1 t2 => trefl (shift k t1 i) (shift k t2 i)

  | tfold T t' => tfold (shift k T i) (shift k t' i)
  | tunfold t' => tunfold (shift k t' i)
  | tunfold_in t1 t2 => tunfold_in (shift k t1 i) (shift (S k) t2 i)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (shift k t1 i) (shift (S k) t2 i)

  | tleft t' => tleft (shift k t' i)
  | tright t' => tright (shift k t' i)
  | sum_match t' tl tr => sum_match (shift k t' i) (shift (S k) tl i) (shift (S k) tr i)

  | typecheck t T => typecheck (shift k t i) (shift k T i)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (shift k T1 i) (shift (S k) T2 i)
  | T_arrow T1 T2 => T_arrow (shift k T1 i) (shift (S k) T2 i)
  | T_sum T1 T2 => T_sum (shift k T1 i) (shift k T2 i)
  | T_refine T p => T_refine (shift k T i) (shift (S k) p i)
  | T_type_refine T1 T2 => T_type_refine (shift k T1 i) (shift (S k) T2 i)
  | T_intersection T1 T2 => T_intersection (shift k T1 i) (shift k T2 i)
  | T_union T1 T2 => T_union (shift k T1 i) (shift k T2 i)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (shift k t1 i) (shift k t2 i)
  | T_forall T1 T2 => T_forall (shift k T1 i) (shift (S k) T2 i)
  | T_exists T1 T2 => T_exists (shift k T1 i) (shift (S k) T2 i)
  | T_abs T => T_abs (shift k T i)
  | T_rec n T0 Ts => T_rec (shift k n i) (shift k T0 i) (shift k Ts i)
  end.

Fixpoint shift_open (k: nat) (t rep: tree) :=
  match t with
  | fvar _ _ => t
  | lvar i term_var => if (PeanoNat.Nat.eq_dec k i) then rep else t
  | lvar i type_var => t
  | notype_err => t
  | err T => err (shift_open k T rep)

  | notype_lambda t' => notype_lambda (shift_open (S k) t' (shift 0 rep 1))
  | lambda T t' => lambda (shift_open k T rep) (shift_open (S k) t' (shift 0 rep 1))
  | app t1 t2 => app (shift_open k t1 rep) (shift_open k t2 rep)

  | forall_inst t1 t2 => forall_inst (shift_open k t1 rep) (shift_open k t2 rep)

  | type_abs t => type_abs (shift_open k t rep)
  | type_inst t T => type_inst (shift_open k t rep) (shift_open k T rep)

  | uu => t

  | tsize t => tsize (shift_open k t rep)

  | pp t1 t2 => pp (shift_open k t1 rep) (shift_open k t2 rep)
  | pi1 t => pi1 (shift_open k t rep)
  | pi2 t => pi2 (shift_open k t rep)

  | because t1 t2 => because (shift_open k t1 rep) (shift_open k t2 rep)
  | get_refinement_witness t1 t2 => get_refinement_witness (shift_open k t1 rep) (shift_open (S k) t2 (shift 0 rep 1))

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (shift_open k t1 rep) (shift_open k t2 rep) (shift_open k t3 rep)
  | boolean_recognizer r t => boolean_recognizer r (shift_open k t rep)

  | zero => t
  | succ t' => succ (shift_open k t' rep)
  | tmatch t' t1 t2 =>
      tmatch
          (shift_open k t' rep)
          (shift_open k t1 rep)
          (shift_open (S k) t2 (shift 0 rep 1))

  | unary_primitive o t => unary_primitive o (shift_open k t rep)
  | binary_primitive o t1 t2 => binary_primitive o (shift_open k t1 rep) (shift_open k t2 rep)

  | tfix T t' => tfix (shift_open (S k) T (shift 0 rep 1)) (shift_open (S (S k)) t' (shift 0 rep 2))
  | notype_tfix t' => notype_tfix (shift_open (S (S k)) t' (shift 0 rep 2))

  | notype_tlet t1 t2 =>
      notype_tlet (shift_open k t1 rep) (shift_open (S k) t2 (shift 0 rep 1))
  | tlet t1 T t2 =>
      tlet (shift_open k t1 rep) (shift_open k T rep) (shift_open (S k) t2 (shift 0 rep 1))
  | trefl t1 t2 => trefl (shift_open k t1 rep) (shift_open k t2 rep)

  | tfold T t' => tfold (shift_open k T rep) (shift_open k t' rep)
  | tunfold t' => tunfold (shift_open k t' rep)
  | tunfold_in t1 t2 => tunfold_in (shift_open k t1 rep) (shift_open (S k) t2 (shift 0 rep 1))
  | tunfold_pos_in t1 t2 => tunfold_pos_in (shift_open k t1 rep) (shift_open (S k) t2 (shift 0 rep 1))

  | tleft t' => tleft (shift_open k t' rep)
  | tright t' => tright (shift_open k t' rep)
  | sum_match t' tl tr => sum_match (shift_open k t' rep) (shift_open (S k) tl (shift 0 rep 1)) (shift_open (S k) tr (shift 0 rep 1))

  | typecheck t T => typecheck (shift_open k t rep) (shift_open k T rep)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (shift_open k T1 rep) (shift_open (S k) T2 (shift 0 rep 1))
  | T_arrow T1 T2 => T_arrow (shift_open k T1 rep) (shift_open (S k) T2 (shift 0 rep 1))
  | T_sum T1 T2 => T_sum (shift_open k T1 rep) (shift_open k T2 rep)
  | T_refine T p => T_refine (shift_open k T rep) (shift_open (S k) p (shift 0 rep 1))
  | T_type_refine T1 T2 => T_type_refine (shift_open k T1 rep) (shift_open (S k) T2 (shift 0 rep 1))
  | T_intersection T1 T2 => T_intersection (shift_open k T1 rep) (shift_open k T2 rep)
  | T_union T1 T2 => T_union (shift_open k T1 rep) (shift_open k T2 rep)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (shift_open k t1 rep) (shift_open k t2 rep)
  | T_forall T1 T2 => T_forall (shift_open k T1 rep) (shift_open (S k) T2 (shift 0 rep 1))
  | T_exists T1 T2 => T_exists (shift_open k T1 rep) (shift_open (S k) T2 (shift 0 rep 1))
  | T_abs T => T_abs (shift_open k T rep)
  | T_rec n T0 Ts => T_rec (shift_open k n rep) (shift_open k T0 rep) (shift_open k Ts rep)
  end.

Lemma is_erased_term_shift:
  forall t k i,
    is_erased_term t ->
    is_erased_term (shift k t i).
Proof.
  induction t; steps.
Qed.

#[export]
Hint Resolve is_erased_term_shift: erased.

Lemma is_erased_term_shift_open:
  forall t k rep,
    is_erased_term t ->
    is_erased_term rep ->
    is_erased_term (shift_open k t rep).
Proof.
  induction t;
    repeat step; eauto with erased.
Qed.

#[export]
Hint Resolve is_erased_term_shift_open: erased.

Lemma is_erased_type_shift:
  forall T k i,
    is_erased_type T ->
    is_erased_type (shift k T i).
Proof.
  induction T; steps; eauto with erased.
Qed.

#[export]
Hint Resolve is_erased_type_shift: erased.

Lemma is_erased_type_shift_open:
  forall T k rep,
    is_erased_type T ->
    is_erased_term rep ->
    is_erased_type (shift_open k T rep).
Proof.
  induction T;
    repeat step; eauto with erased.
Qed.

#[export]
Hint Resolve is_erased_type_shift_open: erased.

Lemma wf_shift:
  forall t k k' k'' i,
    wf t k ->
    k + i <= k'' ->
    wf (shift k' t i) k''.
Proof.
  induction t;
    repeat step; eauto with lia.
Qed.

#[export]
Hint Resolve wf_shift: wf.

Lemma wf_shift_open:
  forall t k rep,
    wf t (S k) ->
    wf rep (S k) ->
    wf (shift_open k t rep) (S k).
Proof.
  induction t;
    try solve [ repeat step; eauto with wf lia ].
Qed.

#[export]
Hint Resolve wf_shift_open: wf.

Lemma wf_shift_open2:
  forall t k i rep,
    i >= k ->
    wf t (S k) ->
    wf rep i ->
    wf (shift_open k t rep) i.
Proof.
  induction t;
    try solve [ repeat step; eauto with wf lia ].
Qed.

#[export]
Hint Resolve wf_shift_open2: wf.

Lemma wf_shift_open3:
  forall t k i rep,
    wf t i ->
    wf rep i ->
    wf (shift_open k t rep) i.
Proof.
  induction t;
    try solve [ repeat step; eauto with wf lia ].
Qed.

#[export]
Hint Resolve wf_shift_open3: wf.

Lemma pfv_shift:
  forall t k i tag,
    pfv t tag = nil ->
    pfv (shift k t i) tag = nil.
Proof.
  induction t;
    repeat step || list_utils.
Qed.

#[export]
Hint Resolve pfv_shift: fv.

Lemma pfv_shift2:
  forall t k i tag,
    pfv (shift k t i) tag = pfv t tag.
Proof.
  induction t;
    repeat step || list_utils.
Qed.

Lemma pfv_shift_open:
  forall t k rep tag,
    pfv t tag = nil ->
    pfv rep tag = nil ->
    pfv (shift_open k t rep) tag = nil.
Proof.
  induction t;
    repeat step || list_utils;
    eauto using pfv_shift.
Qed.

#[export]
Hint Resolve pfv_shift_open: fv.

Lemma pfv_shift_open2:
  forall t k rep tag,
    subset
      (pfv (shift_open k t rep) tag)
      (pfv t tag ++ pfv rep tag).
Proof.
  induction t;
    repeat step || list_utils || sets;
    eauto with sets;
    try solve [
      eapply subset_transitive; eauto; try rewrite pfv_shift2;
      repeat step || sets;
      eauto with sets;
      eauto using subset_left, subset_right, subset_refl
    ].
Qed.

Lemma open_shift:
  forall C t k i,
    wf C (S k) ->
    open k C t = open (k + i) (shift k C i) t.
Proof.
  induction C;
    repeat step || t_equality; eauto with lia wf;
    try solve [ repeat rewrite <- plus_Sn_m; apply_any; auto ].
Qed.

Lemma open_shift_zero:
  forall C t i,
    wf C 1 ->
    open 0 C t = open i (shift 0 C i) t.
Proof.
  intros.
  rewrite <- (plus_O_n i) at 1;
    eauto using open_shift.
Qed.

Lemma shift_nothing:
  forall C k,
    shift k C 0 = C.
Proof.
  induction C; repeat step || rewrite <- plus_n_O in *.
Qed.

Lemma shift_twice:
  forall C k i j,
    shift k (shift k C i) j = shift k C (i + j).
Proof.
  induction C;
    repeat step || rewrite Plus.plus_assoc_reverse; eauto with lia.
Qed.

Lemma open_shift_open:
  forall C1 C2 t k,
    wf C1 (S k) ->
    wf C2 1 ->
    open k C1 (open 0 C2 t) = open k (shift_open k C1 (shift 0 C2 k)) t.
Proof.
  induction C1;
    repeat step || t_equality || rewrite shift_nothing in * || rewrite shift_twice in * || rewrite (PeanoNat.Nat.add_comm k);
    eauto with lia;
    eauto using open_shift_zero.
Qed.

Lemma open_shift_open_zero:
  forall C1 C2 t,
    wf C1 1 ->
    wf C2 1 ->
    open 0 C1 (open 0 C2 t) = open 0 (shift_open 0 C1 C2) t.
Proof.
  intros.
  rewrite <- (shift_nothing C2 0) at 2;
    eauto using open_shift_open.
Qed.

Lemma shift_nothing2:
  forall t k i,
    wf t k ->
    shift k t i = t.
Proof.
  induction t; repeat step || t_equality; eauto with lia.
Qed.

Lemma no_shift_open:
  forall t k rep,
    wf rep 0 ->
    shift_open k t rep = open k t rep.
Proof.
  induction t; repeat step || t_equality || rewrite shift_nothing2 by eauto with wf.
Qed.

Lemma open_and_shift:
  forall t k i j rep,
    wf rep 0 ->
    k >= i ->
    j > 0 ->
    shift i (open k t rep) j = open (j + k) (shift i t j) rep.
Proof.
  intros.
  rewrite Nat.add_comm.
  generalize dependent k.
  generalize dependent i.
  generalize dependent j.
  induction t; repeat step || t_equality || rewrite shift_nothing2 by eauto with wf;
    eauto with lia apply_any.
Qed.

Lemma open_shift_open2:
  forall t k i rep1 rep2,
    wf rep2 0 ->
    wf t (S i) ->
    k >= i ->
    open k (shift_open i t rep1) rep2 = shift_open i t (open k rep1 rep2).
Proof.
  induction t;
    repeat step || t_equality || rewrite open_and_shift by eauto with lia;
    eauto 6 with lia.
Qed.

Lemma substitute_shift:
  forall t k i l tag,
    wfs l 0 ->
    psubstitute (shift k t i) l tag = shift k (psubstitute t l tag) i.
Proof.
  induction t; repeat step || t_equality || rewrite shift_nothing2 by eauto with wf.
Qed.

Lemma shift_open_nothing:
  forall t k i,
    wf t k ->
    shift_open k t i = t.
Proof.
  induction t; repeat step || t_equality; eauto with lia.
Qed.

Lemma open_shift_open3:
  forall t k i rep1 rep2,
    wf rep2 0 ->
    k < i ->
    open k (shift_open i t rep1) rep2 = shift_open i (open k t rep2) (open k rep1 rep2).
Proof.
  induction t;
    repeat step || t_equality ||
           (rewrite shift_open_nothing by eauto with wf) ||
           (rewrite open_and_shift by eauto with lia);
    eauto 6 with lia.
Qed.

Lemma open_shift_open4:
  forall t k rep1 rep2,
    wf rep2 0 ->
    open k (shift_open k t rep1) rep2 = shift_open k t (open k rep1 rep2).
Proof.
  induction t;
    repeat step || t_equality ||
           (rewrite shift_open_nothing by eauto with wf) ||
           (rewrite open_and_shift by eauto with lia);
    eauto 6 with lia.
Qed.

Lemma substitute_shift_open:
  forall t k rep l tag,
    wfs l 0 ->
    pfv rep tag = nil ->
    psubstitute (shift_open k t rep) l tag = shift_open k (psubstitute t l tag) rep.
Proof.
  induction t;
    repeat step || t_equality || apply pfv_shift ||
           (rewrite substitute_nothing5 by auto) ||
           (rewrite shift_open_nothing by eauto with wf) || apply_any.
Qed.

Lemma erase_term_shift:
  forall t k i,
    erase_term (shift k t i) = shift k (erase_term t) i.
Proof.
  induction t; steps.
Qed.

Lemma erase_type_shift:
  forall T k i,
    erase_type (shift k T i) = shift k (erase_type T) i.
Proof.
  induction T; repeat step || rewrite erase_term_shift in *.
Qed.
