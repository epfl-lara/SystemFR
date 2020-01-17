Require Export SystemFR.Trees.
Require Export SystemFR.Tactics.
Require Export SystemFR.Syntax.
Require Export SystemFR.WFLemmas.
Require Export SystemFR.WFLemmasLists.

Require Import PeanoNat.

Require Import Omega.

Opaque Nat.eq_dec.

Fixpoint map_indices (k: nat) (t: tree) (f: nat -> nat) :=
  match t with
  | fvar _ _ => t
  | lvar i term_var => if (Nat.eq_dec k i) then lvar (f i) term_var else t
  | lvar i type_var => t
  | notype_err => t
  | err T => err (map_indices k T f)

  | notype_lambda t' => notype_lambda (map_indices (S k) t' f)
  | lambda T t' => lambda (map_indices k T f) (map_indices (S k) t' f)
  | app t1 t2 => app (map_indices k t1 f) (map_indices k t2 f)

  | forall_inst t1 t2 => forall_inst (map_indices k t1 f) (map_indices k t2 f)

  | type_abs t => type_abs (map_indices k t f)
  | type_inst t T => type_inst (map_indices k t f) (map_indices k T f)

  | uu => t

  | tsize t => tsize (map_indices k t f)

  | pp t1 t2 => pp (map_indices k t1 f) (map_indices k t2 f)
  | pi1 t => pi1 (map_indices k t f)
  | pi2 t => pi2 (map_indices k t f)

  | because t1 t2 => because (map_indices k t1 f) (map_indices k t2 f)
  | get_refinement_witness t1 t2 => get_refinement_witness (map_indices k t1 f) (map_indices (S k) t2 f)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (map_indices k t1 f) (map_indices k t2 f) (map_indices k t3 f)
  | boolean_recognizer r t => boolean_recognizer r (map_indices k t f)

  | zero => t
  | succ t' => succ (map_indices k t' f)
  | notype_rec t' t1 t2 =>
      notype_rec (map_indices k t' f)
                 (map_indices k t1 f)
                 (map_indices (S (S k)) t2 f)
  | rec T t' t1 t2 =>
      rec (map_indices (S k) T f)
          (map_indices k t' f)
          (map_indices k t1 f)
          (map_indices (S (S k)) t2 f)
  | tmatch t' t1 t2 =>
      tmatch
          (map_indices k t' f)
          (map_indices k t1 f)
          (map_indices (S k) t2 f)

  | tfix T t' => tfix (map_indices (S k) T f) (map_indices (S (S k)) t' f)
  | notype_tfix t' => notype_tfix (map_indices (S (S k)) t' f)

  | notype_tlet t1 t2 =>
      notype_tlet (map_indices k t1 f) (map_indices (S k) t2 f)
  | tlet t1 T t2 =>
      tlet (map_indices k t1 f) (map_indices k T f) (map_indices (S k) t2 f)
  | trefl t1 t2 => trefl (map_indices k t1 f) (map_indices k t2 f)

  | tfold T t' => tfold (map_indices k T f) (map_indices k t' f)
  | tunfold t' => tunfold (map_indices k t' f)
  | tunfold_in t1 t2 => tunfold_in (map_indices k t1 f) (map_indices (S k) t2 f)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (map_indices k t1 f) (map_indices (S k) t2 f)

  | tleft t' => tleft (map_indices k t' f)
  | tright t' => tright (map_indices k t' f)
  | sum_match t' tl tr => sum_match (map_indices k t' f) (map_indices (S k) tl f) (map_indices (S k) tr f)

  | typecheck t T => typecheck (map_indices k t f) (map_indices k T f)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (map_indices k T1 f) (map_indices (S k) T2 f)
  | T_arrow T1 T2 => T_arrow (map_indices k T1 f) (map_indices (S k) T2 f)
  | T_sum T1 T2 => T_sum (map_indices k T1 f) (map_indices k T2 f)
  | T_refine T p => T_refine (map_indices k T f) (map_indices (S k) p f)
  | T_type_refine T1 T2 => T_type_refine (map_indices k T1 f) (map_indices (S k) T2 f)
  | T_intersection T1 T2 => T_intersection (map_indices k T1 f) (map_indices k T2 f)
  | T_union T1 T2 => T_union (map_indices k T1 f) (map_indices k T2 f)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (map_indices k t1 f) (map_indices k t2 f)
  | T_forall T1 T2 => T_forall (map_indices k T1 f) (map_indices (S k) T2 f)
  | T_exists T1 T2 => T_exists (map_indices k T1 f) (map_indices (S k) T2 f)
  | T_abs T => T_abs (map_indices k T f)
  | T_rec n T0 Ts => T_rec (map_indices k n f) (map_indices k T0 f) (map_indices k Ts f)
  end.

Definition shift t := map_indices 0 t S.

Lemma open_shift:
  forall t k rep,
    wf t (S k) ->
    open (S k) (map_indices k t S) rep = open k t rep.
Proof.
  induction t; repeat step || t_equality; try omega.
Qed.

Lemma wf_map_succ:
  forall t i k,
    wf t k ->
    i <= k ->
    wf (map_indices i t S) (S k).
Proof.
  induction t; steps; eauto with omega.
Qed.

Lemma wf_shift:
  forall t k,
    wf t k ->
    wf (shift t) (S k).
Proof.
  eauto using wf_map_succ with omega.
Qed.

Hint Resolve wf_shift: wf.

Lemma pfv_map_indices:
  forall t i f tag,
    pfv (map_indices i t f) tag = pfv t tag.
Proof.
  induction t; steps.
Qed.

Lemma map_nothing:
  forall t i f,
    wf t i ->
    map_indices i t f = t.
Proof.
  induction t; repeat step || t_equality; eauto with omega.
Qed.

Lemma psubstitute_map_indices:
  forall t i f l tag,
    wfs l 0 ->
    psubstitute (map_indices i t f) l tag = map_indices i (psubstitute t l tag) f.
Proof.
  induction t; repeat step || t_equality || rewrite map_nothing in *;
    eauto with wf omega.
Qed.
