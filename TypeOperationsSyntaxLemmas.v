Require Import Coq.Strings.String.

Require Export SystemFR.Trees.

Require Export SystemFR.Syntax.


Require Export SystemFR.WFLemmas.
Require Export SystemFR.TWFLemmas.

Require Export SystemFR.FVLemmas.
Require Export SystemFR.AnnotatedTermLemmas.
Require Export SystemFR.Tactics.
Require Export SystemFR.TypeOperations.
Require Export SystemFR.ListUtils.

Lemma is_annotated_type_ite:
  forall b T1 T2 T,
    T_ite_push b T1 T2 T ->
    is_annotated_term b ->
    is_annotated_type T1 ->
    is_annotated_type T2 ->
    is_annotated_type T.
Proof.
  induction 1; steps.
Qed.

Ltac t_is_annotated_type_ite :=
  match goal with
  | H: T_ite_push ?b ?T1 ?T2 ?T |- is_annotated_type ?T => apply is_annotated_type_ite with b T1 T2
  end.

#[global]
Hint Extern 50 => t_is_annotated_type_ite: annot.

Lemma wf_ite:
  forall b T1 T2 T,
    T_ite_push b T1 T2 T ->
    forall k,
      wf b k ->
      wf T1 k ->
      wf T2 k ->
      wf T k.
Proof.
  induction 1; steps; eauto with wf.
Qed.

Ltac t_wf_ite :=
  match goal with
  | H: T_ite_push ?b ?T1 ?T2 ?T |- wf ?T _ => apply wf_ite with b T1 T2
  end.

#[global]
Hint Extern 50 => t_wf_ite: wf.

Lemma twf_ite:
  forall b T1 T2 T,
    T_ite_push b T1 T2 T ->
    forall k,
      twf b k ->
      twf T1 k ->
      twf T2 k ->
      twf T k.
Proof.
  induction 1; steps; eauto with twf.
Qed.

Ltac t_twf_ite :=
  match goal with
  | H: T_ite_push ?b ?T1 ?T2 ?T |- twf ?T _ => apply twf_ite with b T1 T2
  end.

#[global]
Hint Extern 50 => t_twf_ite: twf.

Lemma pfv_ite:
  forall b T1 T2 T,
    T_ite_push b T1 T2 T ->
    forall x tag,
      x ∈ pfv T tag ->
      (x ∈ pfv b tag \/ x ∈ pfv T1 tag \/ x ∈ pfv T2 tag).
Proof.
  induction 1;
    repeat match goal with
           | _ => step || list_utils
           | H1: forall _ _, _ -> _, H2: _ ∈ _ |- _ => pose proof (H1 _ _ H2); clear H2
           end.
Qed.

Ltac t_pfv_ite :=
  match goal with
  | H1: T_ite_push ?b ?T1 ?T2 ?T, H2: ?x ∈ pfv ?T ?tag |- _ =>
    poseNew (Mark H2 "pfv_ite");
    pose proof (pfv_ite _ _ _ _ H1 _ _ H2)
  end.

#[global]
Hint Extern 50 => t_pfv_ite: fv.

Lemma pfv_ite2:
  forall b T1 T2 T S tag,
    T_ite_push b T1 T2 T ->
    subset (pfv b tag) S ->
    subset (pfv T1 tag) S ->
    subset (pfv T2 tag) S ->
    subset (pfv T tag) S.
Proof.
  unfold subset; repeat step || t_pfv_ite.
Qed.

Ltac t_pfv_ite2 :=
  match goal with
  | H: T_ite_push ?b ?T1 ?T2 ?T |- subset (pfv ?T _) _ => apply pfv_ite2 with b T1 T2
  end.

#[global]
Hint Extern 50 => t_pfv_ite2: fv.
