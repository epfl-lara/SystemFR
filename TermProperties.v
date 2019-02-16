Require Import Termination.Syntax.
Require Import Termination.SmallStep.
Require Import Termination.Tactics.
Require Import Termination.StarRelation.
Require Import Termination.WellFormed.

Definition normalizing t: Prop :=
  pfv t term_var = nil /\
  wf t 0 /\
  exists v, is_value v /\ star small_step t v.

Hint Unfold normalizing: props.

Definition irred t :=
  forall t', ~small_step t t'.

Ltac hyp_irred v :=
  match goal with
  | H: irred v |- _ => idtac
  end.
Ltac t_not_hyp_irred t := tryif hyp_irred t then fail else idtac.
