Require Import Termination.Syntax.
Require Import Termination.SmallStep.
Require Import Termination.StarRelation.
Require Import Termination.AssocList.

Definition equivalent t1 t2 :=
  (forall v, is_value v ->
       star small_step t2 v ->
       star small_step t1 v) /\
  (forall v, is_value v ->
       star small_step t1 v ->
       star small_step t2 v).

Definition equivalent_tvars tvars t1 t2 :=
  forall ltypes, support ltypes = tvars ->
            equivalent (substitute t1 ltypes) (substitute t2 ltypes).
