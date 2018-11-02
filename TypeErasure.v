Require Import Termination.Syntax.

(*
(* terms without types *)
Inductive erased_term: Set :=
  (* term or type variable *)
  | e_fvar: nat -> erased_term

  | e_lvar: nat -> erased_term
  | e_err: erased_term

  | e_uu: erased_term
           
  | e_lambda: erased_term -> erased_term
  | e_app: erased_term -> erased_term -> erased_term

  | e_pp: erased_term -> erased_term -> erased_term
  | e_pi1: erased_term -> erased_term
  | e_pi2: erased_term -> erased_term

  | e_ttrue: erased_term             
  | e_tfalse: erased_term
  | e_ite: erased_term -> erased_term -> erased_term -> erased_term

  | e_zero: erased_term
  | e_succ: erased_term -> erased_term 
  | e_rec: erased_term -> erased_term -> erased_term -> erased_term
  | e_tmatch: erased_term -> erased_term -> erased_term -> erased_term

  | e_tlet: erased_term -> erased_term -> erased_term

  | e_trefl: erased_term
.
*)

Fixpoint erase (t: term): term :=
  match t with
  | fvar y => fvar y
  | lvar y => lvar y 
  | err => err

  | uu => uu
            
  | lambda T t' => lambda (erase T) (erase t')
  | app t1 t2 => app (erase t1) (erase t2)
                    
  | pp t1 t2 => pp (erase t1) (erase t2)
  | pi1 t' => pi1 (erase t')
  | pi2 t' => pi2 (erase t')

  | ttrue => ttrue
  | tfalse => tfalse
  | ite t1 t2 t3 => ite (erase t1) (erase t2) (erase t3)
                         
  | zero => zero
  | succ t' => succ (erase t')
  | rec T t' t0 ts => rec (erase T) (erase t') (erase t0) (erase ts)
  | tmatch t' t0 ts => tmatch (erase t') (erase t0) (erase ts)

  | tlet t1 A t2 => tlet (erase t1) (erase A) (erase t2)
  | trefl => trefl

  | T_var _ => T_unit
  | T_unit => T_unit
  | T_bool => T_unit
  | T_nat => T_unit
  | T_refine A p => T_unit
  | T_prod A B => T_unit
  | T_arrow A B => T_unit
  | T_let t A B => T_unit
  | T_singleton t => T_unit
  | T_intersection A B => T_unit
  | T_union A B => T_unit
  | T_top => T_unit
  | T_bot => T_unit
  | T_equal t1 t2 => T_unit
  | T_forall A B => T_unit
  | T_exists A B => T_unit
  end.
