Require Import Coq.Strings.String.

Require Import Termination.Syntax.
Require Import Termination.Sets.
Require Import Termination.ListUtils.
Require Import Termination.Tactics.
Require Import Termination.AssocList.
Require Import Termination.WFLemmas.
Require Import Termination.TermProperties.
Require Import Termination.SmallStep.
Require Import Termination.SizeLemmas.
Require Import Termination.Equivalence.
Require Import Termination.TermForm.
Require Import Termination.StarInversions.
Require Import Termination.TermList.
Require Import Termination.TypeList.
Require Import Termination.TypeErasure.

Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Omega.

Definition reduces_to (P: term -> Prop) (t: term) :=
  wf t 0 /\
  fv t = nil /\
  exists t',
    star small_step t t' /\
    P t'.

Definition index (T: term): option term :=
  match T with
  | _ => None
  end.

Program Fixpoint nat_value_to_nat (v: term) (p: is_nat_value v) :=
  match v with
  | zero => 0
  | succ v' => S (nat_value_to_nat v' _)
  | _ => _
  end.

Solve Obligations with destruct v; repeat light || discriminate.

Lemma nat_value_to_nat_fun:
  forall v p1 p2, nat_value_to_nat v p1 = nat_value_to_nat v p2.
Proof.
  induction v; steps.
Qed.

Definition lt_index (i1 i2: option term) :=
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
  induction m; destruct v; steps; try omega.
  - apply Acc_intro; repeat step || tlu || t_deterministic_star; omega.
  - apply Acc_intro; repeat step || tlu || t_deterministic_star.
    apply IHm with v1 p1; steps.
    rewrite (nat_value_to_nat_fun v p p2) in *; eauto with omega.
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

Notation "p1 '<<' p2" := (lexprod nat (option term) lt lt_index p1 p2) (at level 80).

Opaque lt.

Lemma lt_index_some_none:
  forall i, lt_index (Some i) None.
Proof.
  unfold lt_index; steps; eauto.
Qed.

(* an interpretation for every type variable, as a collection of values *)
Definition interpretation: Type := list (nat * (term -> Prop)).

Equations (noind) reducible_values (theta: interpretation) (v: term) (T: term): Prop :=
  reducible_values theta v T by rec (size T, index T) (lexprod _ _ lt lt_index) :=

  reducible_values theta v (fvar X tag) :=
    if (tag_eq_dec tag type_var)
    then
      match lookup Nat.eq_dec theta X with
      | None => False
      | Some P => P v
      end
    else False;

  reducible_values theta v T_unit := v = uu;

  reducible_values theta v T_bool := v = ttrue \/ v = tfalse;

  reducible_values theta v T_nat := is_nat_value v;

  reducible_values theta v (T_arrow A B) :=
    is_value v /\
    fv v = nil /\
    wf v 0 /\
    forall a (p: term_form a),
      reducible_values theta a A ->
      reduces_to (fun t => reducible_values theta t (open 0 B a)) (app v a);

  reducible_values theta v (T_prod A B) :=
     exists a b (p: term_form a),
       v = pp a b /\
       reducible_values theta a A /\
       reducible_values theta b (open 0 B a);

  reducible_values theta v (T_refine T p) :=
    reducible_values theta v T /\
    wf p 1 /\
    star small_step (open 0 p v) ttrue;

  reducible_values theta v (T_let a A B) :=
    exists a' (p: term_form a'),
      is_value a' /\
      star small_step a a' /\
      reducible_values theta v (open 0 B a');

  reducible_values theta v (T_singleton t) :=
    is_value v /\
    fv v = nil /\
    wf v 0 /\
    star small_step t v;

  reducible_values theta v (T_intersection A B) :=
    reducible_values theta v A /\
    reducible_values theta v B;

  reducible_values theta v (T_union A B) :=
    reducible_values theta v A \/
    reducible_values theta v B;

  reducible_values theta v T_top :=
      is_value v /\ fv v = nil /\ wf v 0 ;

  reducible_values theta v T_bot := False;

  reducible_values theta v (T_equal t1 t2) :=
    v = trefl /\
    equivalent t1 t2;

  reducible_values theta v (T_forall A B) :=
      is_value v /\
      fv v = nil /\
      wf v 0 /\
      forall a (p: term_form a), reducible_values theta a A -> reducible_values theta v (open 0 B a);

  reducible_values theta v (T_exists A B) :=
    exists a (p: term_form a), reducible_values theta a A /\ reducible_values theta v (open 0 B a);

  reducible_values theta v T := False
.

Solve Obligations with (repeat step || autorewrite with bsize; eauto using left_lex with omega).
Fail Next Obligation.

Definition reducible (theta: interpretation) (t: term) (T: term): Prop :=
  reduces_to (fun t => reducible_values theta t T) t.

Fixpoint valid_interpretation (theta: interpretation): Prop :=
  match theta with
  | nil => True
  | (x,P) :: theta' => valid_interpretation theta' /\ forall v, P v -> (is_value v /\ fv v = nil /\ wf v 0)
  end.

Definition open_reducible (tvars: tvar_list) (gamma: context) t T: Prop :=
  forall theta lterms,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma lterms  ->
    support theta = tvars ->
    reducible theta (substitute t lterms) (substitute T lterms).

Lemma in_valid_interpretation_fv: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  pfv v term_var = nil.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_wf: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  wf v 0.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.

Lemma in_valid_interpretation_value: forall theta v X P,
  valid_interpretation theta ->
  lookup Nat.eq_dec theta X = Some P ->
  P v ->
  is_value v.
Proof.
  induction theta; repeat step || eauto || apply_any.
Qed.

Lemma reducibility_rewrite:
  forall theta t T,
    reduces_to (fun t => reducible_values theta t T) t =
    reducible theta t T.
Proof.
  reflexivity.
Qed.

Lemma obvious_reducible:
  forall theta t T,
    reducible theta t T ->
    exists t',
      star small_step t t' /\
      reducible_values theta t' T.
Proof.
  unfold reducible, reduces_to; steps.
Qed.

Ltac simp_red :=
  repeat (
    rewrite reducible_values_equation_1 in * ||
    rewrite reducible_values_equation_2 in * ||
    rewrite reducible_values_equation_3 in * ||
    rewrite reducible_values_equation_4 in * ||
    rewrite reducible_values_equation_5 in * ||
    rewrite reducible_values_equation_6 in * ||
    rewrite reducible_values_equation_7 in * ||
    rewrite reducible_values_equation_8 in * ||
    rewrite reducible_values_equation_9 in * ||
    rewrite reducible_values_equation_10 in * ||
    rewrite reducible_values_equation_11 in * ||
    rewrite reducible_values_equation_12 in * ||
    rewrite reducible_values_equation_13 in * ||
    rewrite reducible_values_equation_14 in * ||
    rewrite reducible_values_equation_15 in * ||
    rewrite reducible_values_equation_16 in * ||
    rewrite reducible_values_equation_17 in * ||
    rewrite reducible_values_equation_18 in * ||
    rewrite reducible_values_equation_19 in * ||
    rewrite reducible_values_equation_20 in * ||
    rewrite reducible_values_equation_21 in * ||
    rewrite reducible_values_equation_22 in * ||
    rewrite reducible_values_equation_23 in * ||
    rewrite reducible_values_equation_24 in * ||
    rewrite reducible_values_equation_25 in * ||
    rewrite reducible_values_equation_26 in * ||
    rewrite reducible_values_equation_27 in * ||
    rewrite reducible_values_equation_28 in * ||
    rewrite reducible_values_equation_29 in * ||
    rewrite reducible_values_equation_30 in * ||
    rewrite reducible_values_equation_31 in * ||
    rewrite reducible_values_equation_32 in * ||
    rewrite reducible_values_equation_33 in *
  ).

Ltac top_level_unfold :=
  match goal with
  | H: reducible _ _ _ |- _ => unfold reducible, reduces_to in H
  end.
