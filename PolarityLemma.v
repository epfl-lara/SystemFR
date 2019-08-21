Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Omega.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import SystemFR.StarInversions.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Syntax.
Require Import SystemFR.Trees.
Require Import SystemFR.Tactics.
Require Import SystemFR.Equivalence.
Require Import SystemFR.OpenTOpen.

Require Import SystemFR.SizeLemmas.

Require Import SystemFR.WFLemmas.
Require Import SystemFR.TWFLemmas.
Require Import SystemFR.ErasedTermLemmas.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.RedTactics.
Require Import SystemFR.ReducibilityMeasure.
Require Import SystemFR.ReducibilitySubst.
Require Import SystemFR.ReducibilityRenaming.
Require Import SystemFR.ReducibilityUnused.
Require Import SystemFR.RedTactics2.

Require Import SystemFR.IdRelation.
Require Import SystemFR.EqualWithRelation.

Require Import SystemFR.EquivalentWithRelation.
Require Import SystemFR.AssocList.
Require Import SystemFR.Sets.
Require Import SystemFR.Freshness.
Require Import SystemFR.SwapHoles.
Require Import SystemFR.ListUtils.
Require Import SystemFR.TOpenTClose.
Require Import SystemFR.NoTypeFVar.

Require Import SystemFR.Polarity.
Require Import SystemFR.PolarityLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.NoTypeFVarLemmas.

Opaque makeFresh.
Opaque Nat.eq_dec.
Opaque reducible_values.


Definition subset_rc (rc1 rc2: tree -> Prop) := forall v, rc1 v -> rc2 v.

Hint Unfold subset_rc: u_short.

Fixpoint respect_polarities pols (theta1 theta2: interpretation) :=
  match theta1, theta2 with
  | nil, nil => True
  | (X, rc1) :: theta1', (Y, rc2) :: theta2' =>
    X = Y /\
    (~((X, Positive) ∈ pols) -> subset_rc rc2 rc1) /\
    (~((X, Negative) ∈ pols) -> subset_rc rc1 rc2) /\
    respect_polarities pols theta1' theta2'
  | _, _ => False
  end.

Lemma respect_polarities_refl:
  forall pols theta,
    respect_polarities pols theta theta.
Proof.
  induction theta; steps.
Qed.

Lemma invert_twice:
  forall pol, invert_polarity (invert_polarity (pol)) = pol.
Proof.
  destruct pol; steps.
Qed.

Lemma pair_in_invert:
  forall (pols : list (nat * polarity)) (x : nat) pol,
    (x, invert_polarity pol) ∈ pols ->
    (x, pol) ∈ invert_polarities pols.
Proof.
  induction pols; repeat step || rewrite invert_twice.
Qed.

Lemma respect_polarities_invert:
  forall pols theta1 theta2,
    respect_polarities pols theta1 theta2 ->
    respect_polarities (invert_polarities pols) theta2 theta1.
Proof.
  induction theta1; repeat step || apply_any || apply pair_in_invert.
Qed.

Ltac t_respect_polarities_invert :=
  match goal with
  | H: respect_polarities _ _ _ |- _ =>
    poseNew (Mark 0 "respect_polarities_invert");
    pose proof (respect_polarities_invert _ _ _ H)
  end.

Definition polarity_variance_prop T: Prop :=
  forall pols theta1 theta2 v,
    has_polarities T pols ->
    respect_polarities pols theta1 theta2 ->
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    reducible_values theta1 v T ->
    reducible_values theta2 v T.

Definition polarity_variance_prop_aux m T: Prop := get_measure T = m -> polarity_variance_prop T.

Definition polarity_variance_until m: Prop := forall m', m' << m -> forall T', polarity_variance_prop_aux m' T'.

Hint Unfold polarity_variance_prop: u_polarity.
Hint Unfold polarity_variance_until: u_polarity.
Hint Unfold polarity_variance_prop_aux: u_polarity.

Lemma use_respect_polarities:
  forall (pols : list (nat * polarity)) (theta1 theta2 : interpretation) (n : nat) (v : tree) P1 P2,
    respect_polarities pols theta1 theta2 ->
    ((n, Negative) ∈ pols -> False) ->
    lookup Nat.eq_dec theta1 n = Some P1 ->
    lookup Nat.eq_dec theta2 n = Some P2 ->
    P1 v ->
    P2 v.
Proof.
  induction theta1; steps; eauto with beapply_any.
Qed.

Lemma respect_polarities_some_none:
  forall (n : nat) (pols : list (nat * polarity)) (theta1 theta2 : interpretation) P,
    respect_polarities pols theta1 theta2 ->
    lookup Nat.eq_dec theta1 n = Some P ->
    lookup Nat.eq_dec theta2 n = None ->
    False.
Proof.
  induction theta1; steps; eauto.
Qed.

Lemma polarity_variance_fvar: forall m n f, polarity_variance_prop_aux m (fvar n f).
Proof.
  repeat autounfold with u_polarity;
    repeat step || destruct_tag || simp_red || step_inversion has_polarities;
    eauto using respect_polarities_some_none.
  eapply use_respect_polarities; eauto 1; steps.
Qed.

Hint Immediate polarity_variance_fvar: b_polarity_variance.

Lemma polarity_variance_induction:
  forall T ci n o pols theta1 theta2 v,
    polarity_variance_until (ci, (n, o)) ->
    respect_polarities pols theta1 theta2 ->
    has_polarities T pols ->
    typeNodes T < n ->
    count_interpret T <= ci ->
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    reducible_values theta1 v T ->
    reducible_values theta2 v T.
Proof.
  repeat autounfold with u_polarity; intros.
  eapply_any; eauto 1; repeat step || apply leq_lt_measure.
Qed.

Lemma polarity_variance_induction_invert:
  forall T ci n o pols theta1 theta2 v,
    polarity_variance_until (ci, (n, o)) ->
    respect_polarities pols theta1 theta2 ->
    has_polarities T (invert_polarities pols) ->
    typeNodes T < n ->
    count_interpret T <= ci ->
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    reducible_values theta2 v T ->
    reducible_values theta1 v T.
Proof.
  repeat autounfold with u_polarity; intros.
  eapply H with _ (invert_polarities pols) theta2; eauto 1; repeat step || apply leq_lt_measure;
    eauto using respect_polarities_invert.
Qed.

Lemma polarity_variance_induction_open:
  forall T a ci n o pols theta1 theta2 v,
    polarity_variance_until (ci, (n, o)) ->
    respect_polarities pols theta1 theta2 ->
    has_polarities T pols ->
    typeNodes T < n ->
    count_interpret T <= ci ->
    is_erased_term a ->
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    is_erased_type T ->
    reducible_values theta1 v (open 0 T a) ->
    reducible_values theta2 v (open 0 T a).
Proof.
  repeat autounfold with u_polarity; intros.
  eapply_any; eauto 1;
    repeat step || apply leq_lt_measure || autorewrite with bsize in * ||
           apply polarity_open.
Qed.

Lemma polarity_variance_arrow:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_arrow T1 T2).
Proof.
  unfold get_measure, polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || t_reduces_to2 || apply_any;
    try solve [ eapply polarity_variance_induction_invert; try eassumption; steps; eauto with omega ];
    try solve [ eapply polarity_variance_induction_open; try eassumption; steps; eauto with omega ].
Qed.

Hint Immediate polarity_variance_arrow: b_polarity_variance.

Lemma polarity_variance_prod:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_prod T1 T2).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || t_reduces_to2 || apply_any || find_exists;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega ];
    try solve [ eapply polarity_variance_induction_open; try eassumption; steps; eauto with omega ].
Qed.

Hint Immediate polarity_variance_prod: b_polarity_variance.

Lemma polarity_variance_sum:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_sum T1 T2).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || find_exists;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega ].
Qed.

Hint Immediate polarity_variance_sum: b_polarity_variance.

Lemma polarity_variance_refine:
  forall m T b, polarity_variance_until m -> polarity_variance_prop_aux m (T_refine T b).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || find_exists;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega ].
Qed.

Hint Immediate polarity_variance_refine: b_polarity_variance.

Lemma polarity_variance_type_refine:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_type_refine T1 T2).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || exists p;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega ];
    try solve [ eapply polarity_variance_induction_open; try eassumption; steps; eauto with omega berased ].
Qed.

Hint Immediate polarity_variance_type_refine: b_polarity_variance.

Lemma polarity_variance_let:
  forall m t T, polarity_variance_until m -> polarity_variance_prop_aux m (T_let t T).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || find_smallstep_value;
    try solve [ eapply polarity_variance_induction_open; try eassumption; steps; eauto with omega berased ].
Qed.

Hint Immediate polarity_variance_let: b_polarity_variance.

Lemma polarity_variance_intersection:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_intersection T1 T2).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega berased ].
Qed.

Hint Immediate polarity_variance_intersection: b_polarity_variance.

Ltac reducibility_choice2 :=
  match goal with
  | H: reducible_values _ ?v ?T1 |- reducible_values _ ?v ?T1 \/ _ => left
  | H: reducible_values _ ?v ?T2 |- _ \/ reducible_values _ ?v ?T2 => right
  end.

Lemma polarity_variance_union:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_union T1 T2).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || reducibility_choice2;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega berased ].
Qed.

Hint Immediate polarity_variance_union: b_polarity_variance.

Lemma polarity_variance_forall:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_forall T1 T2).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities.
  eapply polarity_variance_induction_open; eauto 1; repeat step || apply leq_lt_measure || apply_any;
    try omega;
    try solve [ eapply polarity_variance_induction_invert; try eassumption; steps; eauto with omega berased ].
Qed.

Hint Immediate polarity_variance_forall: b_polarity_variance.

Lemma polarity_variance_exists:
  forall m T1 T2, polarity_variance_until m -> polarity_variance_prop_aux m (T_exists T1 T2).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || exists a;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega berased ];
    try solve [ eapply polarity_variance_induction_open; try eassumption; steps; eauto with omega berased ].
Qed.

Hint Immediate polarity_variance_exists: b_polarity_variance.

Lemma respect_polarities_support:
  forall (pols : list (nat * polarity)) (theta1 theta2 : interpretation) X,
    respect_polarities pols theta1 theta2 ->
    ~(X ∈ support theta1) ->
    X ∈ support theta2 ->
    False.
Proof.
  induction theta1; steps; eauto.
Qed.

Lemma polarity_variance_abs:
  forall m T, polarity_variance_until m -> polarity_variance_prop_aux m (T_abs T).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities.
  exists (makeFresh ((X :: nil) :: support pols :: support theta2 :: pfv T type_var :: nil));
    repeat step; try finisher.

  repeat step || t_instantiate_rc || t_reduces_to.

  lazymatch goal with
  | H: reducible_values _ _ _ |- reducible_values ((?M,?RC) :: _) _ _ =>
    apply (reducible_rename_one _ _ _ _ _ M) in H
  end; repeat step || finisher.

  lazymatch goal with
  | |- reducible_values ((?M,?RC) :: _) _ _ =>
    eapply polarity_variance_induction with _ _ _ pols ((M,RC) :: theta1); eauto 1
  end;
    repeat step || apply leq_lt_measure || autorewrite with bsize in * ||
           apply has_polarities_topen; try finisher.
Qed.

Hint Immediate polarity_variance_abs: b_polarity_variance.

Ltac t_dangerous_rec_choice :=
  match goal with
  | H: star small_step _ zero |- _ \/ _ => left
  | H: star small_step _ (succ _) |- _ => right
  end.


Lemma respect_polarities_cons:
  forall (pols : list (nat * polarity)) (theta1 theta2 : interpretation) X pol,
    respect_polarities pols theta1 theta2 ->
    respect_polarities ((X, pol) :: pols) theta1 theta2.
Proof.
  induction theta1; steps.
Qed.

Lemma polarity_variance_rec:
  forall m tn T0 Ts, polarity_variance_until m -> polarity_variance_prop_aux m (T_rec tn T0 Ts).
Proof.
  unfold polarity_variance_prop_aux, polarity_variance_prop;
    repeat step || simp_red || step_inversion has_polarities || t_dangerous_rec_choice || find_exists;
    try solve [ eapply polarity_variance_induction; try eassumption; steps; eauto with omega berased ].

  define m (makeFresh (pfv T0 type_var :: pfv Ts type_var :: support pols :: support theta1 :: support theta2 :: nil)).
  exists n', m;
    repeat step; try finisher.

  define m (makeFresh (pfv T0 type_var :: pfv Ts type_var :: support pols :: support theta1 :: support theta2 :: nil)).
  apply (reducible_rename_one _ _ _ _ _ m) in H10;
    repeat step;
      eauto using reducibility_is_candidate;
      try finisher.

  define m (makeFresh (pfv T0 type_var :: pfv Ts type_var :: support pols :: support theta1 :: support theta2 :: nil)).
  eapply (polarity_variance_induction _ _ _ _ ((m, Positive) :: pols) ((m, fun t : tree => reducible_values theta1 t (T_rec n' T0 Ts)) :: theta1)); eauto 1;
    repeat step || apply respect_polarities_cons || unfold subset_rc ||
            autorewrite with bsize in *;
    try finisher;
    try solve [ eapply has_polarities_rename_one; eauto 1; steps; try finisher ];
    eauto with omega;
    eauto using reducibility_is_candidate.

  eapply H; eauto 1; repeat step || apply right_lex, right_lex || apply PolRec;
    eauto using lt_index_step.
Qed.

Hint Immediate polarity_variance_rec: b_polarity_variance.

Lemma polarity_variance_aux: forall (m: measure_domain) T, polarity_variance_prop_aux m T.
Proof.
  induction m using measure_induction; destruct T;
    eauto 2 with b_polarity_variance;
    try solve [ repeat autounfold with u_polarity in *;
                repeat step || step_inversion has_polarities || simp_red ].
Qed.

Lemma polarity_variance: forall T, polarity_variance_prop T.
Proof.
  intros; eapply polarity_variance_aux; eauto.
Qed.

Lemma positive_grow:
  forall theta X rc1 rc2 v T pols,
    has_polarities (topen 0 T (fvar X type_var)) ((X, Positive) :: pols) ->
    reducible_values ((X, rc1) :: theta) v (topen 0 T (fvar X type_var)) ->
    subset_rc rc1 rc2 ->
    valid_interpretation theta ->
    reducibility_candidate rc1 ->
    reducibility_candidate rc2 ->
    reducible_values ((X, rc2) :: theta) v (topen 0 T (fvar X type_var)).
Proof.
  intros.
  eapply (polarity_variance _ _ ((X,rc1) :: theta)); eauto 1; steps;
    eauto 2 using respect_polarities_refl.
Qed.
