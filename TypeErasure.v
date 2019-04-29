Require Import Coq.Program.Tactics.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.

Require Import Coq.Strings.String.

Open Scope list_scope.

Fixpoint erase_term (t: tree): tree :=
  match t with
  | fvar y term_var => t
  | lvar y term_var => t
  | err T => notype_err

  | uu => uu

  | tsize t => tsize (erase_term t)

  | lambda T t' => notype_lambda (erase_term t')
  | app t1 t2 => app (erase_term t1) (erase_term t2)

  | forall_inst t1 t2 => erase_term t1

  | pp t1 t2 => pp (erase_term t1) (erase_term t2)
  | pi1 t' => pi1 (erase_term t')
  | pi2 t' => pi2 (erase_term t')

  | because t1 t2 => erase_term t1
  | get_proof_in t1 t2 => notype_tlet uu (erase_term t2)

  | ttrue => ttrue
  | tfalse => tfalse
  | ite t1 t2 t3 => ite (erase_term t1) (erase_term t2) (erase_term t3)
  | boolean_recognizer r t => boolean_recognizer r (erase_term t)

  | zero => zero
  | succ t' => succ (erase_term t')
  | rec T t' t0 ts => notype_rec (erase_term t') (erase_term t0) (erase_term ts)
  | tmatch t' t0 ts => tmatch (erase_term t') (erase_term t0) (erase_term ts)

  | tlet t1 A t2 => notype_tlet (erase_term t1) (erase_term t2)
  | trefl t1 t2 => uu

  | type_abs t => type_abs (erase_term t)
  | type_inst t T => notype_inst (erase_term t)

  | tfix T t => notype_tfix (erase_term t)

  | tfold T t' => notype_tfold (erase_term t')
  | tunfold t' => tunfold (erase_term t')
  | tunfold_in t1 t2 => tunfold_in (erase_term t1) (erase_term t2)

  | tleft t' => tleft (erase_term t')
  | tright t' => tright (erase_term t')
  | sum_match t' tl tr => sum_match (erase_term t') (erase_term tl) (erase_term tr)

  | typecheck t T => erase_term t

  | _ => uu
  end.

Fixpoint erase_type (T: tree): tree :=
  match T with
  | fvar _ type_var => T
  | lvar _ type_var => T
  | T_unit => T
  | T_bool => T
  | T_nat => T
  | T_refine A p => T_refine (erase_type A) (erase_term p)
  | T_type_refine A B => T_type_refine (erase_type A) (erase_type B)
  | T_prod A B => T_prod (erase_type A) (erase_type B)
  | T_arrow A B => T_arrow (erase_type A) (erase_type B)
  | T_sum A B => T_sum (erase_type A) (erase_type B)
  | T_let t B => T_let (erase_term t) (erase_type B)
  | T_singleton t => T_singleton (erase_term t)
  | T_intersection A B => T_intersection (erase_type A) (erase_type B)
  | T_union A B => T_union (erase_type A) (erase_type B)
  | T_top => T
  | T_bot => T
  | T_equal t1 t2 => T_equal (erase_term t1) (erase_term t2)
  | T_forall A B => T_forall (erase_type A) (erase_type B)
  | T_exists A B => T_exists (erase_type A) (erase_type B)
  | T_abs T => T_abs (erase_type T)
  | T_rec n T0 Ts => T_rec (erase_term n) (erase_type T0) (erase_type Ts)
  | _ => T_unit
  end.

Lemma erase_term_erased:
  forall t, is_erased_term (erase_term t).
Proof.
  induction t; steps.
Qed.

Lemma erase_type_erased:
  forall T, is_erased_type (erase_type T).
Proof.
  induction T; steps; eauto using erase_term_erased.
Qed.

Program Fixpoint erase_context (l: list (nat * tree)): list (nat * tree) :=
  match l with
  | nil => nil
  | (x, T) :: l' => (x, erase_type T) :: erase_context l'
  end.

Hint Resolve erase_term_erased: berased.
Hint Resolve erase_type_erased: berased.
