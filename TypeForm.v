Require Import Termination.Tactics.
Require Import Termination.Syntax.


Fixpoint term_form t :=
  match t with
  | fvar y => True
  | lvar i => True
  | err => True

  | uu => True
            
  | lambda T t' => True
  | app t1 t2 => True

  | pp t1 t2 => True
  | pi1 t => True
  | pi2 t => True
                     
  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => True
                     
  | zero => True
  | succ t' => True
  | rec T t' t1 t2 => True
  | tmatch t' t1 t2 => True

  | tlet _ _ _ => True
  | trefl => True

  | T_type => False
  | T_unit => False
  | T_bool => False
  | T_nat => False
  | T_prod T1 T2 => False
  | T_arrow T1 T2 => False
  | T_refine T p => False
  | T_let t A B => False
  | T_singleton t => False
  | T_intersection T1 T2 => False
  | T_union T1 T2 => False
  | T_top => False
  | T_bot => False
  | T_equal t1 t2 => False
  | T_forall T1 T2 => False
  | T_exists T1 T2 => False
  end.

(*
  
Fixpoint type_form T :=
  match T with
  | T_type => True
  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_refine A p => type_form A
  | T_arrow A B => type_form A /\ type_form B
  | T_prod A B => type_form A /\ type_form B 
  | T_let t A B => type_form A /\ type_form B
  | T_singleton t => True
  | T_intersection A B => type_form A /\ type_form B
  | T_union A B => type_form A /\ type_form B
  | T_top => True
  | T_bot => True
  | T_equal _ _ => True
  | T_forall A B => type_form A /\ type_form B
  | T_exists A B => type_form A /\ type_form B

  | _ => False
  end.

Lemma type_form_subst:
  forall B l,
    type_form B -> type_form (substitute B l).
Proof.
  induction B; steps.
Qed.

Hint Resolve type_form_subst: btf. 


Lemma type_form_open:
  forall B k v,
    type_form B -> type_form (open k B v).
Proof.
  induction B; steps.
Qed.

Hint Resolve type_form_open: btf. 

*)