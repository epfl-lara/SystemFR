Require Export SystemFR.Syntax.
Require Export SystemFR.WFLemmas.
From Stdlib Require Import List.
Import ListNotations.
Open Scope bool_scope.

(* Decidable equality for trees *)
Definition fv_tag_dec : forall (x y : fv_tag), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y; try solve [(left; reflexivity) || (right; congruence)].
Defined.

Definition tree_eq_dec : forall (x y : tree), {x = y} + {x <> y}.
Proof.
  repeat decide equality || apply fv_tag_dec.
Defined.
Definition tree_eq t1 t2 : bool := if (tree_eq_dec t1 t2) then true else false.

Lemma tree_eq_prop : forall t1 t2, (tree_eq t1 t2 = true) <-> t1 = t2.
Proof.
  unfold tree_eq.
  steps.
Qed.

Definition mod_tree_eq a b t1 t2 :=
  exists C, t1 = open 0 C a /\ t2 = open 0 C b.


(* If t and t' are equal modulo substitutions of a for b, it returns true
 *)
Fixpoint mod_tree_eqb t1 t2 a b : bool :=
  if (tree_eq t1 t2) then true
  else
    if (tree_eq t1 a && tree_eq t2 b) then true
    else
      match (t1, t2) with
      | (err T1, err T2) => mod_tree_eqb T1 T2 a b
      | (tsize t1, tsize t2) => mod_tree_eqb t1 t2 a b

      | (notype_lambda t1, notype_lambda t2) => mod_tree_eqb t1 t2 a b
      | (lambda T1 t1, lambda T2 t2) => (mod_tree_eqb T1 T2 a b) && (mod_tree_eqb t1 t2 a b)

      | ((pp t11 t12), (pp t21 t22)) => (mod_tree_eqb t11 t21 a b) && (mod_tree_eqb t12 t22 a b)
      | _ => false
      end
.

Lemma mod_tree_eqb_correct :
  forall a b t2 t1,
    wf t1 0 ->
    wf t2 0 ->
    mod_tree_eqb t1 t2 a b = true ->
    mod_tree_eq t1 t2 a b.
Proof.
  unfold mod_tree_eq; intros.
  unfold mod_tree_eqb in H1.
Abort.
