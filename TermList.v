Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Termination.Syntax.
Require Import Termination.Sets.
Require Import Termination.AssocList.
Require Import Termination.Tactics.
Require Import Termination.ListUtils.
Require Import Termination.FVLemmas.
Require Import Termination.SubstitutionLemmas.

Open Scope list_scope.

Inductive satisfies (P: tree -> tree -> Prop):
  list (nat * tree) -> (* gamma *)
  list (nat * tree) -> (* lterms *)
  Prop :=
| SatNil: satisfies P nil nil
| SatCons:
    forall x t T gamma lterms,
      ~(x ∈ fv T) ->
      ~(x ∈ fv_context gamma) ->
      pfv t term_var = nil ->
      pfv t type_var = nil ->
      wf t 0 ->
      twf t 0 ->
      P t (substitute T lterms) ->
      satisfies P gamma lterms ->
      satisfies P ((x,T) :: gamma) ((x,t) :: lterms).

Lemma satisfies_nodup:
  forall P gamma lterms,
    satisfies P gamma lterms ->
    NoDup (support gamma).
Proof.
  induction 1; repeat step; eauto with bfv.
Qed.

Hint Resolve satisfies_nodup: btermlist.

Ltac t_satisfies_nodup :=
  match goal with
  | H: satisfies ?P ?G ?L |- _ =>
    poseNew (Mark (P,G,L) "satisfies_nodup");
    pose proof (satisfies_nodup _ _ _ H)
  end.

Lemma satisfies_lookup:
  forall P gamma lterms,
    satisfies P gamma lterms ->
    forall x t T,
      lookup Nat.eq_dec gamma x = Some T ->
      lookup Nat.eq_dec lterms x = Some t ->
      P t (substitute T lterms).
Proof.
  induction 1; steps; eauto.
  - rewrite substitute_nothing2; eauto.
  - rewrite substitute_cons; eauto.
    apply IHsatisfies with x0; eauto.
    rewrite substitute_nothing; repeat step; eauto with bfv.
Qed.

Lemma satisfies_lookup2:
  forall P gamma lterms x t T,
    satisfies P gamma lterms ->
    lookup Nat.eq_dec gamma x = Some T ->
    lookup Nat.eq_dec lterms x = Some t ->
    P t (substitute T lterms).
Proof.
  intros; eapply satisfies_lookup; eauto.
Qed.

Lemma satisfies_same_support:
  forall P gamma lterms,
    satisfies P gamma lterms ->
    support gamma = support lterms.
Proof.
  induction 1; steps.
Qed.

Hint Resolve satisfies_same_support: btermlist.

(* FIXME: needs to be adapted for type substitutions

Lemma satisfies_subst:
  forall (P: term -> term -> Prop) gamma1 gamma2 l1 l2 x rep T ltypes,
    support gamma1 = support l1 ->
    support gamma2 = support l2 ->
    ~(x ∈ fv T) ->
    ~(x ∈ fv_context gamma2) ->
    ~(x ∈ support l1) ->
    ~(x ∈ support l2) ->
    ~(x ∈ support ltypes) ->
    (forall z, z ∈ support l1 -> z ∈ fv T -> False) ->
    (forall z, z ∈ support l1 -> z ∈ fv rep -> False) ->
    fv (substitute rep l2) = nil ->
    wf (substitute rep l2) 0 ->
    P (substitute rep l2) (substitute T (l2 ++ ltypes)) ->
    satisfies P (substitute_context gamma1 ((x,rep) :: nil) ++ gamma2) (l1 ++ l2) ltypes ->
    satisfies P (gamma1 ++ (x,T) :: gamma2) (l1 ++ (x, substitute rep (l1 ++ l2)) :: l2) ltypes.
Proof.
  induction gamma1; repeat step.
  - destruct l1; repeat step || constructor.
  - destruct l1 as [ | z zs ] eqn:LL;
      repeat match goal with
             | _ => step || t_listutils || step_inversion satisfies || constructor
             | _ => unfold subset in *
             end; eauto with bfv.

    + rewrite substitute_nothing2; steps; eauto.
      rewrite <- substitute_cons3 in *.
      erewrite subst_permutation; eauto.
      eapply obvious_equivalence3.


      eauto using obvious_equivalence3.
    + rewrite substitute_nothing2; steps; eauto.
      apply IHgamma1; repeat step || step_inversion NoDup; eauto.
Qed.
*)

Ltac t_instantiate_sat :=
  match goal with
  | H1: forall lterms, satisfies ?P ?G lterms -> _,
    H2: satisfies ?P ?G _ |- _ =>
      pose proof (H1 _ H2); clear H1
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

Ltac t_satisfies :=
  match goal with
  | |- satisfies _ (_ :: _) (_ :: _) => constructor
  end.

Lemma satisfies_tail:
  forall p gamma1 gamma2 l1 l2,
    satisfies p (gamma1 ++ gamma2) (l1 ++ l2) ->
    support gamma1 = support l1 ->
    satisfies p gamma2 l2.
Proof.
  induction gamma1; destruct l1; repeat step || step_inversion satisfies; eauto.
Qed.

Ltac f_equal_cons :=
  match goal with
  | |- cons _ _ = cons _ _ => f_equal
  end.

Lemma satisfies_cut:
  forall p gamma1 gamma2 lterms,
    satisfies p (gamma1 ++ gamma2) lterms ->
    exists l1 l2,
      lterms = l1 ++ l2 /\
      support gamma1 = support l1 /\
      support gamma2 = support l2 /\
      satisfies p gamma2 l2.
Proof.
  induction gamma1; destruct lterms; steps; repeat step || step_inversion satisfies.
  - exists nil, nil; steps.
  - exists nil, ((n,t) :: lterms);
      repeat step || t_termlist || apply SatCons || f_equal_cons;  eauto with btermlist.
  -  match goal with
     | H: forall gamma2 lterms, _, H2: satisfies _ _ _ |- _ =>
       pose proof (H _ _ H2); steps
     end.
     exists ((n,t) :: l1), l2; repeat step.
Qed.

Ltac t_sat_cut :=
  match goal with
  | H: satisfies ?P (?G1 ++ ?G2) ?L |- _ =>
    poseNew (Mark (P,G1,G2,L) "satisfies_cut");
    pose proof (satisfies_cut _ _ _ _ H)
  end.
