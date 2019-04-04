Require Import SystemFR.Syntax.
Require Import SystemFR.SmallStep.
Require Import SystemFR.StarRelation.
Require Import SystemFR.AssocList.

Definition equivalent t1 t2 :=
  (forall v, is_value v ->
       star small_step t2 v ->
       star small_step t1 v) /\
  (forall v, is_value v ->
       star small_step t1 v ->
       star small_step t2 v).
