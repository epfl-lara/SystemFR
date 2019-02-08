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
Require Import Termination.StarInversions.
Require Import Termination.TermList.
Require Import Termination.TypeErasure.

Require Import Termination.ReducibilityMeasure.
Require Import Termination.ReducibilityCandidate.

Require Import Equations.Equations.
Require Import Equations.Subterm.

Require Import Omega.

Definition closed_term t :=
  pfv t term_var = nil /\
  wf t 0 /\
  is_erased_term t.

Definition closed_value v :=
  closed_term v /\
  is_value v.

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

Equations (noind) reducible_values (theta: interpretation) (v: tree) (T: tree): Prop
    by wf (size T, index T) (lexprod _ _ lt lt_index) :=
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
    closed_value v /\
    forall a (p: is_erased_term a),
      reducible_values theta a A ->
      reduces_to (fun t => reducible_values theta t (open 0 B a)) (app v a);

  reducible_values theta v (T_prod A B) :=
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

  reducible_values theta v (T_let a A B) :=
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
    v = trefl /\
    equivalent t1 t2;

  reducible_values theta v (T_forall A B) :=
    closed_value v /\
    forall a (p: is_erased_term a),
      reducible_values theta a A ->
      reducible_values theta v (open 0 B a);

  reducible_values theta v (T_exists A B) :=
    closed_value v /\
    exists a (_: is_erased_term a),
      reducible_values theta a A /\
      reducible_values theta v (open 0 B a);

  reducible_values theta v (T_rec n T0 Ts) :=
    closed_value v /\
    is_erased_term n /\ (
      (star small_step n zero /\ reducible_values theta v T0) \/
      (exists n' v' X (p1: is_nat_value n') (p2: star small_step n (succ n')),
         v = tfold v' /\
         ~(X ∈ pfv T0 type_var) /\
         ~(X ∈ pfv Ts type_var) /\
         ~(X ∈ support theta) /\
         reducible_values ((X, fun t => reducible_values theta t (T_rec n' T0 Ts)) :: theta)
                          v'
                          (topen 0 Ts (fvar X type_var))
      )
    );

  reducible_values theta v T := False
.

Ltac t_reducibility_definition :=
  repeat step || autorewrite with bsize;
    eauto using left_lex with omega;
    eauto using right_lex, lt_index_step.

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
    rewrite reducible_values_equation_50 in *
  ).

Ltac top_level_unfold :=
  match goal with
  | H: reducible _ _ _ |- _ => unfold reducible, reduces_to in H
  end.
