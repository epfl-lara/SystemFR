Require Import Coq.Strings.String.

Require Import SystemFR.Syntax.
Require Import SystemFR.Sets.
Require Import SystemFR.ListUtils.
Require Import SystemFR.Tactics.
Require Import SystemFR.AssocList.
Require Import SystemFR.WFLemmas.
Require Import SystemFR.TermProperties.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SizeLemmas.
Require Import SystemFR.Equivalence.
Require Import SystemFR.StarInversions.
Require Import SystemFR.TermList.

Require Import SystemFR.StarRelation.

Require Import SystemFR.ReducibilityMeasure.
Require Import SystemFR.ReducibilityCandidate.

Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import Omega.

Definition reduces_to (P: tree -> Prop) (t: tree) :=
  closed_term t /\
  exists t',
    star small_step t t' /\
    P t'.

Lemma reduces_to_equiv:
  forall (P P': tree -> Prop) t,
    reduces_to P t ->
    (forall v, P v -> P' v) ->
    reduces_to P' t.
Proof.
  unfold reduces_to; repeat step || eexists; eauto.
Qed.

Equations reducible_values (theta: interpretation) (v: tree) (T: tree): Prop
    by wf (get_measure T) lt_measure :=
  reducible_values theta v (fvar X type_var) :=
    match lookup Nat.eq_dec theta X with
    | None => False
    | Some P => P v
    end;

  reducible_values theta v T_unit := v = uu;

  reducible_values theta v T_bool := v = ttrue \/ v = tfalse;

  reducible_values theta v T_nat := is_nat_value v;

  reducible_values theta v (T_abs T) :=
    closed_value v /\
    exists X,
      ~(X ∈ support theta) /\
      ~(X ∈ pfv T type_var) /\
      forall RC,
        reducibility_candidate RC ->
        reduces_to (fun t => reducible_values ((X,RC) :: theta) t (topen 0 T (type_fvar X)))
                   (notype_inst v);

  reducible_values theta v (T_arrow A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    forall a (p: is_erased_term a),
      reducible_values theta a A ->
      reduces_to (fun t => reducible_values theta t (open 0 B a)) (app v a);

  reducible_values theta v (T_prod A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    exists a b (_: is_erased_term a),
      v = pp a b /\
      reducible_values theta a A /\
      reducible_values theta b (open 0 B a);

  reducible_values theta v (T_sum A B) :=
    closed_value v /\ (
      (exists v', v = tleft v' /\ reducible_values theta v' A) \/
      (exists v', v = tright v' /\ reducible_values theta v' B)
    );

  reducible_values theta v (T_refine T p) :=
    closed_value v /\
    reducible_values theta v T /\
    is_erased_term p /\
    wf p 1 /\
    star small_step (open 0 p v) ttrue;

  reducible_values theta v (T_type_refine T1 T2) :=
    exists (_: is_erased_type T2),
    exists (_: closed_value v),
      reducible_values theta v T1 /\
      exists p, reducible_values theta p (open 0 T2 v);

  reducible_values theta v (T_let a B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    exists a' (_: is_erased_term a'),
      is_erased_term a /\
      is_value a' /\
      star small_step a a' /\
      reducible_values theta v (open 0 B a');

  reducible_values theta v (T_singleton t) :=
    closed_value v /\
    is_erased_term t /\
    star small_step t v;

  reducible_values theta v (T_intersection A B) :=
    closed_value v /\
    reducible_values theta v A /\
    reducible_values theta v B;

  reducible_values theta v (T_union A B) :=
    closed_value v /\ (
      reducible_values theta v A \/
      reducible_values theta v B
    );

  reducible_values theta v T_top :=
    closed_value v;

  reducible_values theta v T_bot := False;

  reducible_values theta v (T_equal t1 t2) :=
    closed_value v /\
    is_erased_term t1 /\
    is_erased_term t2 /\
    v = uu /\
    equivalent t1 t2;

  reducible_values theta v (T_forall A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    forall a (p: is_erased_term a),
      reducible_values theta a A ->
      reducible_values theta v (open 0 B a);

  reducible_values theta v (T_exists A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    exists a (_: is_erased_term a),
      reducible_values theta a A /\
      reducible_values theta v (open 0 B a);

  reducible_values theta v (T_rec n T0 Ts) :=
    closed_value v /\
    is_erased_term n /\ (
      (exists v', v = notype_tfold v' /\ star small_step n zero /\ reducible_values theta v' T0) \/
      (exists n' v' X (p1: is_nat_value n') (p2: star small_step n (succ n')),
         v = notype_tfold v' /\
         ~(X ∈ pfv T0 type_var) /\
         ~(X ∈ pfv Ts type_var) /\
         ~(X ∈ support theta) /\
         reducible_values ((X, fun t => reducible_values theta t (T_rec n' T0 Ts)) :: theta)
                          v'
                          (topen 0 Ts (fvar X type_var))
      )
    );

  reducible_values theta v (T_interpret T) :=
    closed_value v /\
    exists T' (_: count_interpret T' < 1 + count_interpret T),
      star small_step T T' /\
      irred T' /\
      reducible_values theta v T';

  reducible_values theta v T := False
.

Hint Transparent lt_measure: core.

Ltac t_reducibility_definition :=
  repeat step || autorewrite with bsize || unfold "<<", get_measure, closed_value, closed_term in *;
    try solve [ apply right_lex, right_lex, lt_index_step; steps ];
    try solve [ apply leq_lt_measure; omega ];
    try solve [ apply left_lex; omega ].

Solve Obligations with t_reducibility_definition.

Fail Next Obligation.

Definition reducible (theta: interpretation) t T: Prop :=
  reduces_to (fun t => reducible_values theta t T) t.

Definition open_reducible (tvars: tvar_list) (gamma: context) t T: Prop :=
  forall theta lterms,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma lterms  ->
    support theta = tvars ->
    reducible theta
              (substitute t lterms)
              (substitute T lterms).

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
  rewrite reducible_values_equation_33 in * ||
  rewrite reducible_values_equation_34 in * ||
  rewrite reducible_values_equation_35 in * ||
  rewrite reducible_values_equation_36 in * ||
  rewrite reducible_values_equation_37 in * ||
  rewrite reducible_values_equation_38 in * ||
  rewrite reducible_values_equation_39 in * ||
  rewrite reducible_values_equation_40 in * ||
  rewrite reducible_values_equation_41 in * ||
  rewrite reducible_values_equation_42 in * ||
  rewrite reducible_values_equation_43 in * ||
  rewrite reducible_values_equation_44 in * ||
  rewrite reducible_values_equation_45 in * ||
  rewrite reducible_values_equation_46 in * ||
  rewrite reducible_values_equation_47 in * ||
  rewrite reducible_values_equation_48 in * ||
  rewrite reducible_values_equation_49 in * ||
  rewrite reducible_values_equation_50 in * ||
  rewrite reducible_values_equation_51 in * ||
  rewrite reducible_values_equation_52 in * ||
  rewrite reducible_values_equation_53 in * ||
  rewrite reducible_values_equation_54 in * ||
  rewrite reducible_values_equation_55 in * ||
  rewrite reducible_values_equation_56 in * ||
  rewrite reducible_values_equation_57 in * ||
  rewrite reducible_values_equation_58 in * ||
  rewrite reducible_values_equation_59 in * ||
  rewrite reducible_values_equation_60 in * ||
  rewrite reducible_values_equation_61 in * ||
  rewrite reducible_values_equation_62 in *.

Ltac top_level_unfold :=
  match goal with
  | H: reducible _ _ _ |- _ => unfold reducible, reduces_to in H
  end.
