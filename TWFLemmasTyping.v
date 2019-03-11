Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.TWFLemmas.
Require Import Termination.Typing.
Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.ListUtils.
Require Import Termination.Freshness.
Require Import Termination.WellFormed.

Require Import Termination.BaseType.
Require Import Termination.BaseTypeSyntaxLemmas.

Require Import Termination.TypeOperations.
Require Import Termination.TypeOperationsSyntaxLemmas.

Open Scope list_scope.

Lemma well_typed_twf:
  (forall tvars gamma t T, has_type tvars gamma t T -> twf t 0 /\ twf T 0) /\
  (forall tvars gamma T, is_type tvars gamma T -> twf T 0) /\
  (forall tvars gamma, is_context tvars gamma -> forall x T,
                 lookup Nat.eq_dec gamma x = Some T -> twf T 0) /\
  (forall tvars gamma T1 T2, is_subtype tvars gamma T1 T2 -> twf T1 0 /\ twf T2 0) /\
  (forall tvars gamma t1 t2, are_equal tvars gamma t1 t2 -> twf t1 0 /\ twf t2 0).
Proof.
  apply mut_HT_IT_IC_IS_AE;
  repeat match goal with
           | _ => step || (progress unfold set in *)
           | _ => solve [ repeat (fresh_instantiations0; eauto 1 with omega) ||
                                step; eauto with btwf ]
           end ||
         unshelve eauto with btwf ||
         unshelve eauto with btwf2;
    eauto 3 with step_tactic btwf.
Qed.

Definition has_type_twf_tt := proj1 well_typed_twf.
Definition is_type_twf := proj1 (proj2 well_typed_twf).
Definition is_subtype_twf := proj1 (proj2 (proj2 (proj2 well_typed_twf))).
Definition are_equal_twf := proj2 (proj2 (proj2 (proj2 well_typed_twf))).

Hint Resolve is_type_twf: btwf.

Lemma has_type_twf_term:
  forall tvars gamma t T k, has_type tvars gamma t T -> twf t k.
Proof.
  intros.
  apply twf_monotone with 0; eauto with omega.
  apply (proj1 (has_type_twf_tt tvars gamma t T H)); eauto.
Qed.

Lemma has_type_twf_type:
  forall tvars gamma t T k, has_type tvars gamma t T -> twf T k.
Proof.
  intros.
  apply twf_monotone with 0; eauto with omega.
  apply (proj2 (has_type_twf_tt tvars gamma t T H)); eauto.
Qed.

Hint Resolve has_type_twf_term has_type_twf_type: bwf.

Lemma are_equal_twf_left:
  forall tvars gamma t1 t2 k, are_equal tvars gamma t1 t2 -> twf t1 k.
Proof.
  intros.
  apply twf_monotone with 0; eauto with omega.
  apply (proj1 (are_equal_twf tvars gamma t1 t2 H)); eauto.
Qed.

Lemma are_equal_twf_right:
  forall tvars gamma t1 t2, are_equal tvars gamma t1 t2 -> twf t2 0.
Proof.
  intros.
  apply twf_monotone with 0; eauto with omega.
  apply (proj2 (are_equal_twf tvars gamma t1 t2 H)); eauto.
Qed.

Hint Resolve are_equal_twf_left are_equal_twf_right: btwf.

Lemma has_type_twfs:
  forall tvars P gamma l k,
    satisfies P gamma l ->
    P = has_type tvars nil ->
    twfs l k.
Proof.
  induction 1; steps; eauto using has_type_twf_term.
Qed.

Hint Resolve has_type_twfs: btwf.

Ltac t_twf_info :=
  match goal with
  | H: has_type ?tvars ?G ?t ?T |- _ =>
    poseNew (Mark (tvars,G,t,T) "has_type_twf");
    pose proof (has_type_twf_tt tvars G t T H)
  end.

Ltac t_twf_info_IT :=
  match goal with
  | H: is_type ?tvars ?G ?T |- _ =>
    poseNew (Mark (tvars,G,T) "is_type_twf");
    pose proof (is_type_twf tvars G T H)
  end.
