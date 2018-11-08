Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Sets.
Require Import Termination.SetLemmas.
Require Import Termination.Typing.
Require Import Termination.AssocList.
Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.Freshness.
Require Import Termination.ListUtils.
Require Import Termination.TermList.
Require Import Termination.SmallStep.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasEval.

Lemma subset_singleton_support:
  forall (gamma : context) (x : nat) T,
    lookup Nat.eq_dec gamma x = Some T ->
    subset (singleton x) (support gamma).
Proof.
  repeat step || t_sets; eauto using lookupSupport.    
Qed.

Hint Resolve subset_singleton_support: b_sub_open.

Lemma subset_range_context:
  forall (gamma : context) (x : nat) T S,
    subset (fv_context gamma) S ->
    lookup Nat.eq_dec gamma x = Some T ->
    subset (fv T) S.
Proof.
  eauto using subset_transitive, fv_lookup.
Qed.

Hint Resolve subset_range_context: b_sub_open.

Lemma subset_open:
  forall t rep k S,
    subset (fv (open k t rep)) S ->
    subset (fv t) S.
Proof.
  unfold subset; repeat step || slow_instantiations; eauto 2 with bfv.
Qed.

Lemma subset_open2:
  forall t rep k S,
    subset (fv t) S ->
    subset (fv rep) S ->
    subset (fv (open k t rep)) S.
Proof.
  unfold subset; repeat step.
  apply fv_open2 in H1; repeat step || t_listutils.
Qed.

Lemma in_middle:
  forall A (x: A) (s1 s2: list A),
    x ∈ s1 ++ x :: s2.
Proof.
  induction s1; steps.
Qed.

Hint Immediate in_middle: b_sub_open.

Lemma subset_left:
  forall A (s1 s2 s3: set A),
    subset s1 s2 ->
    subset s1 (s2 ++ s3).
Proof.
  eauto with sets.
Qed.

Lemma in_middle2:
  forall A (x: A) (s1 s2 s3: list A),
    x ∈ (s1 ++ x :: s2) ++ s3.
Proof.
  induction s1; steps.
Qed.

Hint Immediate in_middle2: b_sub_open.

Lemma subset_middle:
  forall A (x: A) (s s1 s2: list A),
    ~(x ∈ s) ->
    subset s (s1 ++ x :: s2) ->
    subset s (s1 ++ s2).
Proof.
  unfold subset; induction s1; repeat step || t_listutils || instantiate_any.
Qed.

Hint Immediate subset_middle: b_sub_open.


Lemma subset_middle2:
  forall A (x y: A) (s s1 s2: list A),
    ~(x ∈ s) ->
    ~(y ∈ s) ->
    subset s (s1 ++ x :: y :: s2) ->
    subset s (s1 ++ s2).
Proof.
  unfold subset; induction s1; repeat step || t_listutils || instantiate_any.
Qed.

Lemma subset_middle3:
  forall A (x y: A) (s s1 s2: list A),
    ~(y ∈ s) ->
    subset s (s1 ++ x :: y :: s2) ->
    subset s (s1 ++ x :: s2).
Proof.
  unfold subset; induction s1; repeat step || t_listutils || instantiate_any.
Qed.

Lemma subset_middle4:
  forall A (x y z: A) (s s1 s2: list A),
    ~(y ∈ s) ->
    ~(z ∈ s) ->
    subset s (s1 ++ x :: y :: z :: s2) ->
    subset s (s1 ++ x :: s2).
Proof.
  unfold subset; induction s1; repeat step || t_listutils || instantiate_any.
Qed.

Lemma subset_middle5:
  forall A (x: A) (s s1 s2 s3: list A),
    ~(x ∈ s) ->
    subset s ((s1 ++ x :: s2) ++ s3) ->
    subset s ((s1 ++ s2) ++ s3).
Proof.
  unfold subset; induction s1; repeat step || t_listutils || instantiate_any.
Qed.

Lemma subset_middle6:
  forall A (x y: A) (s s1 s2 s3: list A),
    ~(x ∈ s) ->
    ~(y ∈ s) ->
    subset s ((s1 ++ x :: y :: s2) ++ s3) ->
    subset s ((s1 ++ s2) ++ s3).
Proof.
  unfold subset; induction s1; repeat step || t_listutils || instantiate_any.
Qed.

Hint Immediate subset_middle5: b_sub_open.

Lemma subset_middle7:
  forall A (x y: A) (s s1 s2 s3: list A),
    ~(y ∈ s) ->
    subset s ((s1 ++ x :: y :: s2) ++ s3) ->
    subset s ((s1 ++ x :: s2) ++ s3).
Proof.
  unfold subset; induction s1; repeat step || t_listutils || instantiate_any.
Qed.

Lemma subset_middle_indirect:
  forall A (s1 s2: list A),
    subset s2 (s1 ++ s2).
Proof.
  intros; eauto with sets.
Qed.
  
Hint Immediate subset_middle_indirect: b_sub_open.

Lemma subset_middle_indirect2:
  forall A (x: A) (s1 s2: list A),
    subset s2 (s1 ++ x :: s2).
Proof.
  intros; eauto with sets.
Qed.
  
Hint Immediate subset_middle_indirect2: b_sub_open.

Lemma subset_right:
  forall A (s1 s2 s3: set A),
    subset s1 s3 ->
    subset s1 (s2 ++ s3).
Proof.
  eauto with sets.
Qed.

Lemma subset_right2:
  forall A x (s1 s2 s3: set A),
    subset s1 s3 ->
    subset s1 (s2 ++ x :: s3).
Proof.
  eauto with sets.
Qed.

Lemma subset_right3:
  forall A x (s1 s2 s3 s4: set A),
    subset s1 s3 ->
    subset s1 ((s2 ++ x :: s3) ++ s4).
Proof.
  eauto using subset_left with sets.
Qed.

Lemma subset_right4:
  forall A x (s1 s2 s3 s4: set A),
    subset s1 (s3 ++ s4) ->
    subset s1 ((s2 ++ x :: s3) ++ s4).
Proof.
  repeat step || t_listutils || unfold subset in * || instantiate_any.
Qed.

Lemma subset_right5:
  forall A x (s1 s2: set A),
    subset s1 s2 ->
    subset s1 (x :: s2).
Proof.
  eauto with sets.
Qed.

Lemma subset_right6:
  forall A (s s1 s2 s3: set A),
    subset s (s2 ++ s3) ->
    subset s ((s1 ++ s2) ++ s3).
Proof.
  repeat step || t_listutils || unfold subset in * || instantiate_any.
Qed.

Hint Immediate subset_right: b_sub_open.
Hint Immediate subset_right2: b_sub_open.
Hint Immediate subset_right3: b_sub_open.
Hint Immediate subset_right4: b_sub_open.
Hint Immediate subset_right5: b_sub_open.
Hint Immediate subset_right6: b_sub_open.

Ltac t_subset_open :=
  match goal with
  | H: subset (fv (open _ _ _)) ?S |- _ =>
    apply subset_open in H 
  end.

Lemma defined_FV:
  (forall tvars gamma t T,
    has_type tvars gamma t T ->
      subset (fv t) (support gamma) /\
      subset (fv T) (support gamma)  /\
      subset (fv_context gamma) (support gamma)
  ) /\
  (forall tvars gamma T,
    is_type tvars gamma T ->
      subset (fv T) (support gamma) /\
      subset (fv_context gamma) (support gamma)
  ) /\
  (forall tvars gamma,
    is_context tvars gamma ->
      subset (fv_context gamma) (support gamma)
  ) /\
  (forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
      subset (fv T1) (support gamma) /\
      subset (fv T2) (support gamma) /\ 
      subset (fv_context gamma) (support gamma) 
  ) /\
  (forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
      subset (fv t1) (support gamma) /\
      subset (fv t2) (support gamma) /\
      subset (fv_context gamma) (support gamma) 
  ).

Proof.
  apply mut_HT_IT_IC_IS_AE;
    repeat match goal with
    | _ => t_subset_open 
    | _ => step
    | _ => solve [ apply subset_left; eauto 2 with b_sub_open; eauto 2 with bfv ]
    | _ => solve [ eauto 2 with b_sub_open ]
    | _ => solve [ eauto 2 with sets ]
    | _ => solve [ eauto 2 with bfv ]
    | _ => solve [ eauto 2 using subset_middle2 ]
    | _ => solve [ eauto 2 using subset_middle3 ]
    | _ => solve [ eauto 2 using subset_middle4 ]
    | _ => solve [ eauto 2 using subset_middle5 ]
    | _ => solve [ eauto 2 using subset_middle6 ]
    | _ => solve [ eauto 2 using subset_middle7 ]
    | _ => progress rewrite subset_add
    | _ => progress rewrite <- subset_union3 in *
    | _ => progress rewrite supportAppend, fv_context_append in *
    | _ => solve [ eapply subset_transitive; eauto using fv_open; repeat step || t_sets ]
    end.
Qed.

Definition defined_FV_HT := proj1 defined_FV.
Definition defined_FV_IT := proj1 (proj2 defined_FV).
Definition defined_FV_IC := proj1 (proj2 (proj2 defined_FV)).
Definition defined_FV_IS := proj1 (proj2 (proj2 (proj2 defined_FV))).
Definition defined_FV_AE := proj2 (proj2 (proj2 (proj2 defined_FV))).

Lemma defined_FV_IT_1:
  forall tvars gamma T,
    is_type tvars gamma T ->
    subset (fv T) (support gamma).
Proof.
  apply defined_FV_IT.
Qed.

Lemma defined_FV_HT_1:
  forall tvars gamma t T,
    has_type tvars gamma t T ->
    subset (fv t) (support gamma).
Proof.
  apply defined_FV_HT.
Qed.

Lemma defined_FV_HT_2:
  forall tvars gamma t T,
    has_type tvars gamma t T ->
    subset (fv T) (support gamma).
Proof.
  apply defined_FV_HT.
Qed.

Lemma defined_FV_HT_3:
  forall tvars gamma t T,
    has_type tvars gamma t T ->
    subset (fv_context gamma) (support gamma).
Proof.
  apply defined_FV_HT.
Qed.

Lemma defined_FV_IS_1:
  forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
    subset (fv T1) (support gamma).
Proof.
  apply defined_FV_IS.
Qed.

Lemma defined_FV_IS_2:
  forall tvars gamma T1 T2,
    is_subtype tvars gamma T1 T2 ->
    subset (fv T2) (support gamma).
Proof.
  apply defined_FV_IS.
Qed.

Lemma defined_FV_AE_1:
  forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    subset (fv t1) (support gamma).
Proof.
  apply defined_FV_AE.
Qed.

Lemma defined_FV_AE_2:
  forall tvars gamma t1 t2,
    are_equal tvars gamma t1 t2 ->
    subset (fv t2) (support gamma).
Proof.
  apply defined_FV_AE.
Qed.

Hint Resolve defined_FV_IT_1: bfv.

Hint Resolve defined_FV_HT_1: bfv.
Hint Resolve defined_FV_HT_2: bfv.
Hint Resolve defined_FV_HT_3: bfv.

Hint Resolve defined_FV_IC: bfv.

Hint Resolve defined_FV_IS_1: bfv.
Hint Resolve defined_FV_IS_2: bfv.

Hint Resolve defined_FV_AE_1: bfv.
Hint Resolve defined_FV_AE_2: bfv.

Ltac p_fv :=
  match goal with
  | H: lookup _ ?G ?x = Some ?T |- _ =>
    poseNew (Mark (G,x,T) "fv_lookup");
    poseNew (fv_lookup _ _ _ H)
  | H: has_type ?tvars ?G ?t ?T |- _ =>
    poseNew (Mark (tvars,G,t,T) "definedFV_HT");
    poseNew (defined_FV_HT _ _ _ _ H)
  | H: is_type ?tvars ?G ?T |- _ =>
    poseNew (Mark (tvars,G,T) "definedFV_IT");
    poseNew (defined_FV_IT _ _ _ H)
  end.

Ltac p_sub_fv :=
  match goal with
  | H: is_subtype ?tvars ?G ?T1 ?T2 |- _ =>
    poseNew (Mark (tvars,G,T1,T2) "definedFV_HT");
    poseNew (defined_FV_IS _ _ _ _ H)
  end.
