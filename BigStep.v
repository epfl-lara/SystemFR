Require Import SystemFR.Trees.
Require Import SystemFR.Syntax.

Reserved Notation "t '~~>*' v" (at level 20).

Inductive bcbv_step: tree -> tree -> Prop :=
  (* const *)
  | BSuu : uu ~~>* uu
  | BSttrue : ttrue ~~>* ttrue
  | BStfalse : tfalse ~~>* tfalse
  | BSzero : zero ~~>* zero

  (* lambda *)
  | BSlambda : forall t, 
      notype_lambda t ~~>* notype_lambda t 
  | BSapp : forall t1 b1 t2 v2 v,
      t1 ~~>* notype_lambda b1 ->
      t2 ~~>* v2 ->
      open 0 b1 v2 ~~>* v ->
        app t1 t2 ~~>* v
where "t '~~>*' v" := (bcbv_step t v).

