Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Export SystemFR.Syntax.

Require Export SystemFR.AssocList.
Require Export SystemFR.Tactics.
Require Export SystemFR.ListUtils.
Require Export SystemFR.FVLemmas.
Require Export SystemFR.SubstitutionLemmas.


Open Scope list_scope.

Inductive satisfies (P: tree -> tree -> Prop):
  list (nat * tree) -> (* Γ *)
  list (nat * tree) -> (* lterms *)
  Prop :=
| SatNil: satisfies P nil nil
| SatCons:
    forall x t T Γ lterms,
      ~(x ∈ fv T) ->
      ~(x ∈ fv_context Γ) ->
      pfv t term_var = nil ->
      pfv t type_var = nil ->
      wf t 0 ->
      twf t 0 ->
      P t (substitute T lterms) ->
      satisfies P Γ lterms ->
      satisfies P ((x,T) :: Γ) ((x,t) :: lterms).

Lemma satisfies_nodup:
  forall P Γ lterms,
    satisfies P Γ lterms ->
    NoDup (support Γ).
Proof.
  induction 1; repeat step; eauto with fv.
Qed.

#[global]
Hint Immediate satisfies_nodup: btermlist.

Ltac t_satisfies_nodup :=
  match goal with
  | H: satisfies ?P ?G ?L |- _ =>
    poseNew (Mark (P,G,L) "satisfies_nodup");
    pose proof (satisfies_nodup _ _ _ H)
  end.

Lemma satisfies_lookup:
  forall P Γ lterms,
    satisfies P Γ lterms ->
    forall x t T,
      lookup PeanoNat.Nat.eq_dec Γ x = Some T ->
      lookup PeanoNat.Nat.eq_dec lterms x = Some t ->
      P t (substitute T lterms).
Proof.
  induction 1; steps; eauto.
  - rewrite substitute_nothing2; eauto.
  - rewrite substitute_cons; eauto.
    apply IHsatisfies with x0; eauto.
    rewrite substitute_nothing; repeat step; eauto with fv.
Qed.

Lemma satisfies_lookup2:
  forall P Γ lterms x t T,
    satisfies P Γ lterms ->
    lookup PeanoNat.Nat.eq_dec Γ x = Some T ->
    lookup PeanoNat.Nat.eq_dec lterms x = Some t ->
    P t (substitute T lterms).
Proof.
  intros; eapply satisfies_lookup; eauto.
Qed.

Lemma satisfies_same_support:
  forall P Γ lterms,
    satisfies P Γ lterms ->
    support Γ = support lterms.
Proof.
  induction 1; steps.
Qed.

#[global]
Hint Immediate satisfies_same_support: btermlist.

Ltac t_instantiate_sat :=
  match goal with
  | H1: forall lterms, satisfies ?P ?G lterms -> _,
    H2: satisfies ?P ?G _ |- _ =>
      pose proof (H1 _ H2); clear H1
  | H1: forall g lterms, satisfies ?P _ lterms -> _,
    H2: satisfies ?P _ _ |- _ =>
      pose proof (H1 _ _ H2); clear H1
end.

Ltac t_termlist :=
  match goal with
  | _ => t_instantiate_sat
  | H: satisfies ?P ?G ?l |- _ =>
      poseNew (Mark (G,l) "same support");
      pose proof (satisfies_same_support _ _ _ H)
  | H1: lookup _ ?g ?x = Some ?T,
    H2: lookup _ ?l ?x = Some ?t,
    H3: satisfies ?p ?g ?l |- _ =>
      poseNew (Mark (p,T) "satisfies");
      pose proof (satisfies_lookup _ _ _ H3 _ _ _ H1 H2)
  end.

Lemma var_in_support:
  forall x P Γ l,
    satisfies P Γ l ->
    ~(x ∈ support Γ) ->
    x ∈ support l ->
    False.
Proof.
  repeat step || t_termlist.
Qed.

Ltac t_satisfies :=
  match goal with
  | |- satisfies _ (_ :: _) (_ :: _) => constructor
  end.

Lemma satisfies_tail:
  forall p Γ1 Γ2 l1 l2,
    satisfies p (Γ1 ++ Γ2) (l1 ++ l2) ->
    support Γ1 = support l1 ->
    satisfies p Γ2 l2.
Proof.
  induction Γ1; destruct l1; repeat step || step_inversion satisfies; eauto.
Qed.

Lemma satisfies_cut:
  forall p Γ1 Γ2 lterms,
    satisfies p (Γ1 ++ Γ2) lterms ->
    exists l1 l2,
      lterms = l1 ++ l2 /\
      support Γ1 = support l1 /\
      support Γ2 = support l2 /\
      satisfies p Γ2 l2.
Proof.
  induction Γ1; destruct lterms; steps; repeat step || step_inversion satisfies.
  - exists nil, nil; steps.
  - exists nil, ((n,t) :: lterms);
      repeat step || t_termlist || apply SatCons;  eauto with btermlist.
  - t_instantiate_sat; steps.
    exists ((n,t) :: l1), l2; repeat step.
Qed.

Ltac satisfies_cut :=
  match goal with
  | H: satisfies ?P (?G1 ++ ?G2) ?L |- _ =>
    poseNew (Mark (P,G1,G2,L) "satisfies_cut");
    pose proof (satisfies_cut _ _ _ _ H)
  end.

Lemma satisfies_fair_split:
  forall P Γ1 Γ2 l1 l2 x t T,
    satisfies P (Γ1 ++ (x, T) :: Γ2) (l1 ++ (x, t) :: l2) ->
    support Γ1 = support l1.
Proof.
  induction Γ1;
    repeat step || step_inversion satisfies || t_termlist || rewrite fv_context_append in * || list_utils.

  - destruct l1; repeat step || t_satisfies_nodup || rewrite support_append in *.
    exfalso. apply H5.
    apply fv_context_support.
    rewrite_any; auto using in_middle.

  - destruct l1; repeat step || t_satisfies_nodup || rewrite support_append in * || t_equality;
      eauto.
Qed.

Lemma x_not_in_support:
  forall P Γ1 Γ2 l x T,
    satisfies P (Γ1 ++ (x, T) :: Γ2) l ->
    x ∈ support Γ1 ->
    False.
Proof.
  repeat step || t_satisfies_nodup || rewrite support_append in *;
    eauto using NoDup_append with step_tactic.
Qed.

#[global]
Hint Immediate x_not_in_support: fv.

Lemma x_not_in_support2:
  forall P Γ1 Γ2 l1 l2 x t T,
    satisfies P (Γ1 ++ (x, T) :: Γ2) (l1 ++ (x, t) :: l2) ->
    x ∈ support l1 ->
    False.
Proof.
  intros.
  erewrite <- satisfies_fair_split in *; eauto;
    eauto using x_not_in_support.
Qed.

#[global]
Hint Immediate x_not_in_support2: fv.

Lemma satisfies_y_in_support:
  forall P Γ1 Γ2 l1 l2 x y t T,
    satisfies P (Γ1 ++ (x, T) :: Γ2) (l1 ++ (x, t) :: l2) ->
    y ∈ support l1 ->
    y ∈ support Γ1.
Proof.
  intros.
  erewrite satisfies_fair_split; eauto.
Qed.

#[global]
Hint Immediate satisfies_y_in_support: fv.

