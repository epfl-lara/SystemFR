Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TypeForm.

Require Import Omega.

(* measure for ensuring termination of reducible_values *)
Fixpoint size T: nat :=
  match T with
  | T_type => 0
  | T_unit => 0
  | T_bool => 0
  | T_nat => 0
  | T_refine A p => 1 + size A
  | T_arrow A B => 3 + size A + size B
  | T_prod A B => 3 + size A + size B 
  | T_let t A B => 2 + size A + size B
  | T_singleton t => 0
  | T_intersection A B => 1 + size A + size B
  | T_union A B => 1 + size A + size B
  | T_top => 0
  | T_bot => 0
  | T_equal _ _ => 0
  | T_forall A B => 3 + size A + size B
  | T_exists A B => 3 + size A + size B

  | _ => 0
  end.

Lemma size_term_form:
  forall t, term_form t -> size t = 0.
Proof.
  destruct t; steps.
Qed.
  
Lemma size_opening:
  forall T k rep, term_form rep -> size (open k T rep) = size T.
Proof.
  induction T;
    repeat match goal with
           | H: forall x, _ |- _ => rewrite H by auto
           | _ => step
           end;
    eauto with omega;
    eauto using size_term_form.
Qed.
  
  (*
Lemma size_opening:
  forall T k rep, type_form T -> size (open k T rep) = size T.
Proof.
  induction T;
    repeat match goal with
           | _ => step
           | H: forall x, _ |- _ => rewrite H by auto
           end; eauto with omega.
Qed.

*)
Hint Rewrite size_opening: bsize.

(* Hint Extern 50 => autorewrite with bsize in *: bsize. *)
