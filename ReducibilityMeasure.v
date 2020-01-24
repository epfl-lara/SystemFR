Require Import Psatz.
Require Import Omega.

Require Export SystemFR.StarInversions.
Require Export SystemFR.SizeLemmas.
Require Export SystemFR.RewriteTactics.

Require Import Equations.Equations.
Require Import Equations.Prop.Subterm. (* lexicographic ordering *)

Require Import Coq.Program.Program.

(* Lexicographic order used for the termination argument of reducibility *)
(* Follows the lexicographic order definition given in Equations *)
(* The measure used is: (size, recursive index) *)

Definition index (T: tree): tree :=
  match T with
  | T_rec n _ _ => n
  | _ => notype_err
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

Unset Program Mode.

Lemma nat_value_to_nat_fun:
  forall v p1 p2, nat_value_to_nat v p1 = nat_value_to_nat v p2.
Proof.
  induction v; repeat step || step_inversion is_nat_value.
Qed.

Definition lt_index (t1 t2: tree) :=
  exists v1 v2 (p1: is_nat_value v1) (p2: is_nat_value v2),
     star scbv_step t1 v1 /\
     star scbv_step t2 v2 /\
     nat_value_to_nat v1 p1 < nat_value_to_nat v2 p2
.

Ltac tlu :=
  match goal with
  | H: lt_index _ _ |- _ => unfold lt_index in H
  end.

Lemma acc_ind_aux:
  forall m t v (p: is_nat_value v),
    nat_value_to_nat v p < m ->
    star scbv_step t v ->
    Acc lt_index t.
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

Lemma acc_ind:
  forall n, Acc lt_index n.
Proof.
  intro; apply Acc_intro; repeat step || tlu; eauto using acc_ind_aux.
Qed.

Lemma wf_lt_index: well_founded lt_index.
Proof.
  unfold well_founded.
  destruct a; repeat step; eauto using acc_ind.
Qed.

Instance wellfounded_lt_index :
  WellFounded lt_index := wf_lt_index.

Definition lt_partial := (lexprod nat tree lt lt_index).
Definition wf_measure_partial := wellfounded_lexprod nat tree lt lt_index lt_wf wf_lt_index.

Opaque lt.

Definition measure_domain: Type := (nat * tree).
Definition lt_measure: measure_domain -> measure_domain -> Prop := lt_partial.
Notation "p1 '<<' p2" := (lt_measure p1 p2) (at level 80).

Lemma leq_lt_measure:
  forall a1 b1 a2 b2,
    a1 <= a2 ->
    lt_index b1 b2 ->
    (a1, b1) << (a2, b2).
Proof.
  unfold "<<", lt_partial; intros;
  destruct (Nat.eq_dec a1 a2); steps; eauto using right_lex; eauto using left_lex with lia.
Qed.

Lemma measure_induction:
  forall P,
    (forall m, (forall m', m' << m -> P m') -> P m) ->
    (forall m, P m).
Proof.
  repeat step || unfold measure_domain in *.
  pose proof (wf_measure_partial (a, b)) as H.
  induction H; steps.
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
    star scbv_step t (succ v) ->
    is_nat_value v ->
    lt_index v t.
Proof.
  unfold lt_index; intros.
  unshelve eexists v, (succ v), _, _; steps;
    eauto with is_nat_value;
    eauto using nat_value_to_nat_succ.
Qed.

Definition get_measure (T: tree) := (type_nodes T, index T).

Lemma leq_lt_measure':
  forall a1 b1 c1 a2 b2 c2,
    a1 <= a2 ->
    b1 < b2 ->
    lexprod nat (nat * tree) lt lt_partial (a1, (b1, c1)) (a2, (b2, c2)).
Proof.
  intros.
  destruct (Nat.eq_dec a1 a2); steps.
  - apply right_lex, left_lex; omega.
  - apply left_lex; omega.
Qed.

Lemma leq_leq_lt_measure:
  forall a1 b1 c1 a2 b2 c2,
    a1 <= a2 ->
    b1 <= b2 ->
    lt_index c1  c2 ->
    lexprod nat (nat * tree) lt lt_partial (a1, (b1, c1)) (a2, (b2, c2)).
Proof.
  intros.
  destruct (Nat.eq_dec a1 a2);
  destruct (Nat.eq_dec b1 b2); steps;
    eauto using right_lex, left_lex with omega.
  - apply right_lex, right_lex; steps.
  - apply right_lex, left_lex; omega.
Qed.

Lemma type_nodes_get_measure:
  forall T1 T2,
    type_nodes T1 < type_nodes T2 ->
    get_measure T1 << get_measure T2.
Proof.
  unfold get_measure; intros; apply left_lex; auto.
Qed.

Hint Extern 1 => solve [
  apply left_lex; repeat step || autorewrite with bsize; eauto 2 with lia; t_closer
]: measure.

Hint Extern 1 => solve [
  apply right_lex; steps; eauto using lt_index_step
]: measure.

Definition prop_at (P: tree -> Prop) m T := get_measure T = m -> P T.

Definition prop_until (P: tree -> Prop) (m: measure_domain): Prop :=
  forall m', m' << m -> forall T, prop_at P m' T.

Lemma prop_until_at:
  forall P m T,
    prop_until P m ->
    get_measure T << m ->
    P T.
Proof.
  unfold prop_until, prop_at;
    steps; eauto.
Qed.

Hint Extern 1 => solve [ eapply prop_until_at; eauto with measure ]: prop_until.
