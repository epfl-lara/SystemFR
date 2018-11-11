Require Import Termination.Syntax.
Require Import Termination.SmallStep.
Require Import Termination.Tactics.
Require Export Termination.StarRelation.

Definition normalizing (t: term): Prop :=
  pfv t term_var = nil /\
  wf t 0 /\
  exists v, is_value v /\ star small_step t v.

Hint Unfold normalizing: props.

Definition irred (t: term) :=
  forall t', ~small_step t t'.

Ltac hyp_irred v :=
  match goal with
  | H: irred v |- _ => idtac
  end.
Ltac t_not_hyp_irred t := tryif hyp_irred t then fail else idtac.
