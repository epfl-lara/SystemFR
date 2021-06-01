Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.
Require Import SystemFR.RewriteTactics.

Reserved Notation "t '~~>*' v" (at level 20).

Inductive bcbv_step: tree -> tree -> Prop :=
  (* const *)
  | BSuu : uu ~~>* uu
  | BSttrue : ttrue ~~>* ttrue
  | BStfalse : tfalse ~~>* tfalse
  | BSzero : zero ~~>* zero
  | BSsucc : forall t v,
    t ~~>* v ->
      succ t ~~>* succ v
  (* lambda *)
  | BSlambda : forall t, 
      notype_lambda t ~~>* notype_lambda t 
  | BSapp : forall t1 b1 t2 v2 v,
      t1 ~~>* notype_lambda b1 ->
      t2 ~~>* v2 ->
      open 0 b1 v2 ~~>* v ->
        app t1 t2 ~~>* v
where "t '~~>*' v" := (bcbv_step t v).

#[global]
Hint Constructors bcbv_step : bcbv_step.

Lemma bs_closed_term: forall t1 t2, t1 ~~>* t2 -> closed_term t1 -> closed_term t2.
Proof.
  induction 1; repeat light || apply_any; t_closer.
Qed.

Lemma bs_value: forall t v, t ~~>* v -> cbv_value v.
Proof.
  induction 1; repeat light; auto with values.
Qed.

Lemma value_bs: forall v, cbv_value v -> v ~~>* v .
Proof.
  induction 1.
Admitted.

#[global]
Hint Immediate bs_value value_bs : values.

Lemma bs_unique: forall t v1 v2, 
  t ~~>* v1 -> 
  t ~~>* v2 ->
    v1 = v2.
Proof.
  intros; generalize dependent v2;
  induction H; inversion 1; 
  repeat light || t_equality || instantiate_any || invert_constructor_equalities. 
Qed.

(* Equivalance small step*)

Lemma ss_bs: forall t1 t2, t1 ~> t2 -> 
  forall v, t2 ~~>* v -> t1 ~~>* v.
Proof.
  induction 1; repeat light.
Admitted.


