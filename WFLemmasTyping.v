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
  (forall gamma t T, has_type gamma t T -> wf t 0 /\ wf T 0) /\
  (forall gamma T, is_type gamma T -> wf T 0) /\
  (forall gamma, is_context gamma -> forall x T,
                 lookup Nat.eq_dec gamma x = Some T -> wf T 0) /\
  (forall gamma T1 T2, is_subtype gamma T1 T2 -> wf T1 0 /\ wf T2 0) /\
  (forall gamma t1 t2, are_equal gamma t1 t2 -> wf t1 0 /\ wf t2 0).
Proof.
  apply mut_HT_IT_IC_IS_AE;
  repeat match goal with
           | _ => step || (progress unfold set in *)
           | _ => solve [ repeat (fresh_instantiations0; eauto 1 with omega) ||
                                step; eauto with bwf ]
           end; eauto with bwf.
Qed.

Definition has_type_wf_tt := proj1 well_typed_wf.
Definition is_type_wf := proj1 (proj2 well_typed_wf).
Definition is_subtype_wf := proj1 (proj2 (proj2 (proj2 well_typed_wf))).
Definition are_equal_wf := proj2 (proj2 (proj2 (proj2 well_typed_wf))).

Hint Resolve is_type_wf: bwf.
(* Hint Resolve is_subtype_wf: bwf. *)

Lemma has_type_wf_term:
  forall gamma t T, has_type gamma t T -> wf t 0.
Proof.
  apply has_type_wf_tt.
Qed.
  
Lemma has_type_wf_type:
  forall gamma t T, has_type gamma t T -> wf T 0.
Proof.
  apply has_type_wf_tt.
Qed.  

Hint Resolve has_type_wf_term has_type_wf_type: bwf.

Lemma are_equal_wf_left:
  forall gamma t1 t2, are_equal gamma t1 t2 -> wf t1 0.
Proof.
  apply are_equal_wf.
Qed.
  
Lemma are_equal_wf_right:
  forall gamma t1 t2, are_equal gamma t1 t2 -> wf t2 0.
Proof.
  apply are_equal_wf.
Qed.

Hint Resolve are_equal_wf_left are_equal_wf_right: bwf.


Lemma wf_coquant:
  forall L U gamma t T,
    (forall x, (x ∈ L -> False) -> has_type ((x, U) :: gamma) (open 0 t (fvar x)) T) ->
    wf t 1.
Proof.
  steps; eauto with bwf.
Qed.

Lemma wf_coquant2:
  forall L U gamma t T,
    (forall x, (x ∈ L -> False) -> has_type ((x, U) :: gamma) (open 0 t (fvar x)) (open 0 T (fvar x))) ->
    wf t 1.
Proof.
  steps; eauto with bwf.
Qed.

Lemma wf_coquant3:
  forall L gamma t T A,
    (forall x y,
        (x ∈ L -> False) ->
        (y ∈ L -> False) ->
        (x = y -> False) ->
        has_type ((x, open 0 T (fvar y)) :: (y, A) :: gamma)
                 (open 0 (open 1 t (fvar y)) (fvar x))
                 (open 0 T (succ (fvar y)))) ->

    wf t 2.
Proof.
  repeat step || fresh_instantiations L; eauto with bwf.
Qed.

Lemma wf_coquant6:
  forall L gamma t A F B,
    (forall x y,
        (x ∈ L -> False) ->
        (y ∈ L -> False) ->
        (x = y -> False) ->
        has_type ((x, F y) :: (y, A) :: gamma)
                 (open 0 (open 1 t (fvar y)) (fvar x))
                 (B y)) ->

    wf t 2.
Proof.
  repeat step || fresh_instantiations L; eauto with bwf.
Qed.

Lemma wf_coquant7:
  forall L gamma t A F B,
    (forall x y,
        (x ∈ L -> False) ->
        (y ∈ L -> False) ->
        (x = y -> False) ->
        has_type ((x, F y) :: (y, A) :: gamma)
                 (open 0 t (fvar y))
                 (B y)) ->

    wf t 1.
Proof.
  repeat step || fresh_instantiations L; eauto with bwf.
Qed.

Lemma wf_coquant4:
  forall L U gamma T,
    (forall x,
        (x ∈ L -> False) ->
        is_type ((x, U) :: gamma) (open 0 T (fvar x))) ->
    wf T 1.
Proof.
  steps; eauto with bwf.
Qed.

Lemma wf_coquant5:
  forall L U gamma t T,
    (forall x, (x ∈ L -> False) -> has_type ((x, U) :: gamma) t T) ->
    wf t 0.
Proof.
  steps; eauto with bwf.
Qed.

Hint Immediate wf_coquant: bwf.
Hint Immediate wf_coquant2: bwf.
Hint Immediate wf_coquant3: bwf.
Hint Immediate wf_coquant4: bwf.
Hint Immediate wf_coquant5: bwf.

Lemma has_type_wfs:
  forall P gamma l,
    satisfies P gamma l ->
    P = has_type nil ->
    wfs l 0.
Proof.
  induction 1; steps; eauto using has_type_wf.
Qed.

Hint Resolve has_type_wfs: bwf.


Ltac t_wf_info :=
  match goal with
  | H: has_type ?G ?t ?T |- _ =>
    poseNew (Mark (G,t,T) "has_type_wf");
    pose proof (has_type_wf_tt G t T H)
  end.

Ltac t_wf_info_IT :=
  match goal with
  | H: is_type ?G ?T |- _ =>
    poseNew (Mark (G,T) "is_type_wf");
    pose proof (is_type_wf G T H)
  end.