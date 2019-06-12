Require Import SystemFR.Syntax.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Tactics.
Require Import SystemFR.StarRelation.
Require Import SystemFR.StarInversions.

Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Coq.Program.Program.

(* Lexicographic order used for the termination argument of reducibility *)
(* Follows a lexicographic order defined in Equations *)

Require Import Omega.

Definition index (T: tree): option tree :=
  match T with
  | T_rec n _ _ => Some n
  | _ => None
  end.

Set Program Mode.

Fixpoint nat_value_to_nat (v: tree) (p: is_nat_value v): nat :=
  match v with
  | zero  => 0
  | succ v' => S (nat_value_to_nat v' _)
  | _ => False_rec nat _
  end.

Ltac destruct_is_nat_value :=
  match goal with
  | H: is_nat_value ?v |- _ =>
     is_var v;
     destruct H
  end.

Ltac t_nat_value_to_nat :=
  repeat program_simpl || step || step_inversion is_nat_value;
    try solve [ destruct_is_nat_value; repeat step ].

Solve Obligations with t_nat_value_to_nat.

Fail Next Obligation.

Lemma nat_value_to_nat_fun:
  forall v p1 p2, nat_value_to_nat v p1 = nat_value_to_nat v p2.
Proof.
  induction v; repeat step || step_inversion is_nat_value.
Qed.

Definition lt_index (i1 i2: option tree) :=
  (exists n, i1 = Some n /\ i2 = None) \/
  (exists n1 n2 v1 v2 (p1: is_nat_value v1) (p2: is_nat_value v2),
     i1 = Some n1 /\
     i2 = Some n2 /\
     star small_step n1 v1 /\
     star small_step n2 v2 /\
     nat_value_to_nat v1 p1 < nat_value_to_nat v2 p2)
.

Ltac tlu :=
  match goal with
  | H: lt_index _ _ |- _ => unfold lt_index in H
  end.

Lemma acc_ind:
  forall m n v (p: is_nat_value v),
    nat_value_to_nat v p < m ->
    star small_step n v ->
    Acc lt_index (Some n).
Proof.
  induction m; destruct p; steps; try omega.
  - apply Acc_intro; repeat step || tlu || t_deterministic_star || simp nat_value_to_nat in *; try omega.
  - apply Acc_intro; repeat step || tlu || t_deterministic_star || simp nat_value_to_nat in *.
    apply IHm with v1 p1; steps.
    match goal with
    | H1: context[nat_value_to_nat ?t ?p1],
      H2: context[nat_value_to_nat ?t ?p2] |- _ =>
      rewrite (nat_value_to_nat_fun t p1 p2) in *
    end; eauto with omega.
Qed.

Lemma acc_ind_some:
  forall n, Acc lt_index (Some n).
Proof.
  intro; apply Acc_intro; repeat step || tlu; eauto using acc_ind.
Qed.

Lemma acc_ind_none:
  Acc lt_index None.
Proof.
  apply Acc_intro; repeat step || tlu; eauto using acc_ind_some.
Qed.

Lemma wf_lt_index: well_founded lt_index.
Proof.
  unfold well_founded.
  destruct a; repeat step; eauto using acc_ind_some, acc_ind_none.
Qed.

Instance wellfounded_lt_index :
  WellFounded lt_index := wf_lt_index.

Notation "p1 '<<' p2" := (lexprod nat (option tree) lt lt_index p1 p2) (at level 80).

Definition wf_measure := wellfounded_lexprod nat (option tree) lt lt_index lt_wf wf_lt_index.

Opaque lt.

Lemma measure_induction:
  forall P,
    (forall m, (forall m', m' << m -> P m') -> P m) ->
    (forall m, P m).
Proof.
  repeat step.
  pose proof (wf_measure (a,b)).
  induction H; steps.
Qed.

Lemma lt_index_some_none:
  forall i, lt_index (Some i) None.
Proof.
  unfold lt_index; steps; eauto.
Qed.

Lemma nat_value_to_nat_succ:
  forall t p1 p2,
    nat_value_to_nat t p1 < nat_value_to_nat (succ t) p2.
Proof.
  repeat step || simp nat_value_to_nat in *.
    match goal with
    | |- context[nat_value_to_nat ?t?p]  =>
      rewrite (nat_value_to_nat_fun t p1 p) in *
    end; eauto with omega.
Qed.

Lemma lt_index_step:
  forall t v,
    star small_step t (succ v) ->
    is_nat_value v ->
    lt_index (Some v) (Some t).
Proof.
  unfold lt_index; right.
  unshelve eexists v, t, v, (succ v), _, _; steps;
    eauto with b_inv;
    eauto using nat_value_to_nat_succ.
Qed.
