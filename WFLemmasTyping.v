Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.WFLemmas.
Require Import Termination.Typing.
Require Import Termination.Tactics.
Require Import Termination.Syntax.
Require Import Termination.AssocList.
Require Import Termination.Sets.
Require Import Termination.TermList.
Require Import Termination.ListUtils.
Require Import Termination.Freshness.
Require Import Termination.WFLemmasEval.

Open Scope list_scope.

Lemma well_typed_wf:
  (forall tvars gamma t T, has_type tvars gamma t T -> wf t 0 /\ wf T 0) /\
  (forall tvars gamma T, is_type tvars gamma T -> wf T 0) /\
  (forall tvars gamma, is_context tvars gamma -> forall x T,
                 lookup Nat.eq_dec gamma x = Some T -> wf T 0) /\
  (forall tvars gamma T1 T2, is_subtype tvars gamma T1 T2 -> wf T1 0 /\ wf T2 0) /\
  (forall tvars gamma t1 t2, are_equal tvars gamma t1 t2 -> wf t1 0 /\ wf t2 0).
Proof.
  apply mut_HT_IT_IC_IS_AE;
  repeat match goal with
           | _ => step || (progress unfold set in * )
           | _ => solve [ repeat (fresh_instantiations0; eauto 1 with omega) ||
                                step; eauto with bwf ]
           end;
      eauto with bwf bwft;
      eauto 3 with step_tactic bwf bwft.
Qed.

Definition has_type_wf_tt := proj1 well_typed_wf.
Definition is_type_wf := proj1 (proj2 well_typed_wf).
Definition is_subtype_wf := proj1 (proj2 (proj2 (proj2 well_typed_wf))).
Definition are_equal_wf := proj2 (proj2 (proj2 (proj2 well_typed_wf))).

Hint Resolve is_type_wf: bwf.
(* Hint Resolve is_subtype_wf: bwf. *)

Lemma has_type_wf_term:
  forall tvars gamma t T k, has_type tvars gamma t T -> wf t k.
Proof.
  intros.
  apply wf_monotone with 0; eauto with omega.
  apply (proj1 (has_type_wf_tt tvars gamma t T H)); eauto.
Qed.

Lemma has_type_wf_type:
  forall tvars gamma t T k, has_type tvars gamma t T -> wf T k.
Proof.
  intros.
  apply wf_monotone with 0; eauto with omega.
  apply (proj2 (has_type_wf_tt tvars gamma t T H)); eauto.
Qed.

Hint Resolve has_type_wf_term has_type_wf_type: bwf.

Lemma are_equal_wf_left:
  forall tvars gamma t1 t2 k, are_equal tvars gamma t1 t2 -> wf t1 k.
Proof.
  intros.
  apply wf_monotone with 0; eauto with omega.
  apply (proj1 (are_equal_wf tvars gamma t1 t2 H)); eauto.
Qed.

Lemma are_equal_wf_right:
  forall tvars gamma t1 t2, are_equal tvars gamma t1 t2 -> wf t2 0.
Proof.
  intros.
  apply wf_monotone with 0; eauto with omega.
  apply (proj2 (are_equal_wf tvars gamma t1 t2 H)); eauto.
Qed.

Hint Resolve are_equal_wf_left are_equal_wf_right: bwf.

Lemma has_type_wfs:
  forall tvars P gamma l k,
    satisfies P gamma l ->
    P = has_type tvars nil ->
    wfs l k.
Proof.
  induction 1; steps; eauto using has_type_wf_term.
Qed.

Hint Resolve has_type_wfs: bwf.

Ltac t_wf_info :=
  match goal with
  | H: has_type ?tvars ?G ?t ?T |- _ =>
    poseNew (Mark (tvars,G,t,T) "has_type_wf");
    pose proof (has_type_wf_tt tvars G t T H)
  end.

Ltac t_wf_info_IT :=
  match goal with
  | H: is_type ?tvars ?G ?T |- _ =>
    poseNew (Mark (tvars,G,T) "is_type_wf");
    pose proof (is_type_wf tvars G T H)
  end.
