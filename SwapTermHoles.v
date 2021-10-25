Require Import PeanoNat.
Require Import Psatz.

Require Export SystemFR.TWFLemmas.
Require Export SystemFR.ErasedTermLemmas.

Opaque PeanoNat.Nat.eq_dec.

Fixpoint swap_term_holes t i j :=
  match t with
  | fvar _ _ => t
  | lvar k term_var =>
    if (PeanoNat.Nat.eq_dec k i)
    then lvar j term_var
    else if (PeanoNat.Nat.eq_dec k j)
    then lvar i term_var
    else t
  | lvar k type_var => t

  | notype_err => t
  | err T => err (swap_term_holes T i j)

  | notype_lambda t' => notype_lambda (swap_term_holes t' (S i) (S j))
  | lambda T t' => lambda (swap_term_holes T i j) (swap_term_holes t' (S i) (S j))
  | app t1 t2 => app (swap_term_holes t1 i j) (swap_term_holes t2 i j)

  | forall_inst t1 t2 => forall_inst (swap_term_holes t1 i j) (swap_term_holes t2 i j)

  | type_abs t => type_abs (swap_term_holes t i j)
  | type_inst t T => type_inst (swap_term_holes t i j) (swap_term_holes T i j)

  | uu => t

  | tsize t => tsize (swap_term_holes t i j)

  | pp t1 t2 => pp (swap_term_holes t1 i j) (swap_term_holes t2 i j)
  | pi1 t => pi1 (swap_term_holes t i j)
  | pi2 t => pi2 (swap_term_holes t i j)

  | because t1 t2 => because (swap_term_holes t1 i j) (swap_term_holes t2 i j)
  | get_refinement_witness t1 t2 =>
    get_refinement_witness (swap_term_holes t1 i j) (swap_term_holes t2 (S i) (S j))

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (swap_term_holes t1 i j) (swap_term_holes t2 i j) (swap_term_holes t3 i j)
  | boolean_recognizer r t => boolean_recognizer r (swap_term_holes t i j)

  | zero => t
  | succ t' => succ (swap_term_holes t' i j)
  | tmatch t' t1 t2 =>
      tmatch
          (swap_term_holes t' i j)
          (swap_term_holes t1 i j)
          (swap_term_holes t2 (S i) (S j))

  | unary_primitive o t => unary_primitive o (swap_term_holes t i j)
  | binary_primitive o t1 t2 => binary_primitive o (swap_term_holes t1 i j) (swap_term_holes t2 i j)

  | tfix T t' => tfix (swap_term_holes T (S i) (S j)) (swap_term_holes t' (S (S i))  (S (S j)))
  | notype_tfix t' => notype_tfix (swap_term_holes t' (S (S i)) (S (S j)))

  | notype_tlet t1 t2 =>
      notype_tlet (swap_term_holes t1 i j) (swap_term_holes t2 (S i) (S j))
  | tlet t1 T t2 =>
      tlet (swap_term_holes t1 i j) (swap_term_holes T i j) (swap_term_holes t2 (S i) (S j))

  | trefl t1 t2 => trefl (swap_term_holes t1 i j) (swap_term_holes t2 i j)

  | tfold T t => tfold (swap_term_holes T i j) (swap_term_holes t i j)
  | tunfold t => tunfold (swap_term_holes t i j)
  | tunfold_in t1 t2 => tunfold_in (swap_term_holes t1 i j) (swap_term_holes t2 (S i) (S j))
  | tunfold_pos_in t1 t2 => tunfold_pos_in (swap_term_holes t1 i j) (swap_term_holes t2 (S i) (S j))

  | tleft t' => tleft (swap_term_holes t' i j)
  | tright t' => tright (swap_term_holes t' i j)
  | sum_match t' tl tr =>
    sum_match (swap_term_holes t' i j)
              (swap_term_holes tl (S i) (S j))
              (swap_term_holes tr (S i) (S j))

  | typecheck t T => typecheck (swap_term_holes t i j) (swap_term_holes T i j)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (swap_term_holes T1 i j) (swap_term_holes T2 (S i) (S j))
  | T_arrow T1 T2 => T_arrow (swap_term_holes T1 i j) (swap_term_holes T2 (S i) (S j))
  | T_sum T1 T2 => T_sum (swap_term_holes T1 i j) (swap_term_holes T2 i j)
  | T_refine T p => T_refine (swap_term_holes T i j) (swap_term_holes p (S i) (S j))
  | T_type_refine T1 T2 => T_type_refine (swap_term_holes T1 i j) (swap_term_holes T2 (S i) (S j))
  | T_intersection T1 T2 => T_intersection (swap_term_holes T1 i j) (swap_term_holes T2 i j)
  | T_union T1 T2 => T_union (swap_term_holes T1 i j) (swap_term_holes T2 i j)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (swap_term_holes t1 i j) (swap_term_holes t2 i j)
  | T_forall T1 T2 => T_forall (swap_term_holes T1 i j) (swap_term_holes T2 (S i) (S j))
  | T_exists T1 T2 => T_exists (swap_term_holes T1 i j) (swap_term_holes T2 (S i) (S j))
  | T_abs T => T_abs (swap_term_holes T i j)
  | T_rec n T0 Ts =>
    T_rec (swap_term_holes n i j) (swap_term_holes T0 i j) (swap_term_holes Ts i j)
  end.

Lemma swap_term_holes_open:
  forall t j1 j2 rep1 rep2,
    j1 <> j2 ->
    wf rep1 0 ->
    wf rep2 0 ->
    open j1 (open j2 t rep2) rep1 =
    open j1 (open j2 (swap_term_holes t j1 j2) rep1) rep2.
Proof.
  induction t;
    repeat step || t_equality || (rewrite open_none by eauto with wf lia);
    eauto with wf lia.
Qed.

Lemma open_twice:
  forall t j1 j2 rep1 rep2,
    j1 <> j2 ->
    wf rep1 0 ->
    wf rep2 0 ->
    open j1 (open j2 t rep2) rep1 =
    open j2 (open j1 t rep1) rep2.
Proof.
  induction t;
    repeat step || open_none || t_equality || apply_any.
Qed.

Lemma swap_term_holes_nothing:
  forall t k i j,
    wf t k ->
    k <= i ->
    k <= j ->
    swap_term_holes t i j = t.
Proof.
  induction t; repeat step || t_equality; eauto with lia.
Qed.

Lemma is_erased_swap_term_holes:
  forall t i j,
    is_erased_term t ->
    is_erased_term (swap_term_holes t i j).
Proof.
  induction t; repeat step || apply_any || rewrite (swap_nothing _ 0).
Qed.

#[export]
Hint Resolve is_erased_swap_term_holes: erased.

Lemma is_erased_type_swap_term_holes:
  forall T i j,
    is_erased_type T ->
    is_erased_type (swap_term_holes T i j).
Proof.
  induction T; repeat step || apply_any || rewrite (swap_nothing _ 0);
    eauto with erased.
Qed.

#[export]
Hint Resolve is_erased_type_swap_term_holes: erased.

Lemma wf_swap_term_holes:
  forall t k rep,
    wf rep 0 ->
    wf t (S k) ->
    wf (open (S k) (swap_term_holes t k (S k)) rep) k.
Proof.
  induction t; steps; eauto with wf lia.
Qed.

#[export]
Hint Resolve wf_swap_term_holes: wf.

Lemma wf_swap_term_holes_2:
  forall t k rep,
    wf rep 0 ->
    wf t (S (S k)) ->
    wf (open (S k) (swap_term_holes t k (S k)) rep) (S k).
Proof.
  induction t; repeat step || unshelve eauto with wf lia.
Qed.

#[export]
Hint Resolve wf_swap_term_holes_2: wf.

Lemma wf_swap_term_holes_3:
  forall t k i j,
    i < k ->
    j < k ->
    wf t k ->
    wf (swap_term_holes t i j) k.
Proof.
  induction t; repeat step || unshelve eauto with wf lia.
Qed.

#[export]
Hint Resolve wf_swap_term_holes_3: wf.

Lemma twf_swap_term_holes:
  forall t k i j,
    twf t k ->
    twf (swap_term_holes t i j) k.
Proof.
  induction t; steps.
Qed.

#[export]
Hint Resolve twf_swap_term_holes: twf.

Lemma swap_term_holes_twice:
  forall t i j,
    swap_term_holes (swap_term_holes t i j) i j = t.
Proof.
  induction t; steps.
Qed.

Lemma pfv_swap_term_holes:
  forall t i j tag, pfv (swap_term_holes t i j) tag = pfv t tag.
Proof.
  induction t; steps.
Qed.

#[export]
Hint Extern 1 => rewrite pfv_swap_term_holes: fv.

Lemma swap_term_holes_open_2:
  forall t i j rep,
    wf rep 0 ->
    open i (swap_term_holes t j i) rep =
    swap_term_holes (open j t rep) j i.
Proof.
  induction t; repeat step || t_equality || rewrite (swap_term_holes_nothing _ 0);
    try lia.
Qed.

Lemma swap_term_holes_open_3:
  forall t k i j rep,
    wf rep 0 ->
    k <> i ->
    k <> j ->
    open k (swap_term_holes t j i) rep =
    swap_term_holes (open k t rep) j i.
Proof.
  induction t; repeat step || t_equality;
    eauto with lia;
    try solve [ erewrite swap_term_holes_nothing; eauto with lia ].
Qed.
