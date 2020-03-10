Require Import Coq.Strings.String.

Require Export SystemFR.TermList.
Require Export SystemFR.ReducibilityMeasure.
Require Export SystemFR.ReducibilityCandidate.

Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.
Require Import Coq.Classes.RelationClasses.

Require Import Omega.

Definition reduces_to (P: tree -> Prop) (t: tree) :=
  closed_term t /\
  exists v, P v /\ star scbv_step t v.

Lemma reduces_to_equiv:
  forall (P P': tree -> Prop) t,
    reduces_to P t ->
    (forall v, P v -> P' v) ->
    reduces_to P' t.
Proof.
  unfold reduces_to; repeat step; eauto.
Qed.

Equations (noind) reducible_values (theta: interpretation) (v: tree) (T: tree): Prop
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
        reducible_values ((X,RC) :: theta) v (topen 0 T (fvar X type_var));

  reducible_values theta v (T_arrow A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    forall a (p: is_erased_term a),
      wf a 0 ->
      pfv a term_var = nil ->
      reducible_values theta a A ->
      reduces_to (fun t => reducible_values theta t (open 0 B a)) (app v a);

  reducible_values theta v (T_prod A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    exists a b (_: is_erased_term a),
      wf a 0 /\
      pfv a term_var = nil /\
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
    pfv p term_var = nil /\
    star scbv_step (open 0 p v) ttrue;

  reducible_values theta v (T_type_refine T1 T2) :=
    exists (_: is_erased_type T2),
    exists (_: closed_value v),
      reducible_values theta v T1 /\
      exists p, reducible_values theta p (open 0 T2 v);

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

  reducible_values theta v (T_equiv t1 t2) :=
    v = uu /\
    equivalent_terms t1 t2;

  reducible_values theta v (T_forall A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    forall a (p: is_erased_term a),
      wf a 0 ->
      pfv a term_var = nil ->
      reducible_values theta a A ->
      reducible_values theta v (open 0 B a);

  reducible_values theta v (T_exists A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    exists a (_: is_erased_term a),
      wf a 0 /\
      pfv a term_var = nil /\
      reducible_values theta a A /\
      reducible_values theta v (open 0 B a);

  reducible_values theta v (T_rec n T0 Ts) :=
    closed_value v /\
    is_erased_term n /\ (
      (star scbv_step n zero /\ reducible_values theta v T0) \/
      (exists n' X (p1: is_nat_value n') (p2: star scbv_step n (succ n')),
         ~(X ∈ pfv T0 type_var) /\
         ~(X ∈ pfv Ts type_var) /\
         ~(X ∈ support theta) /\
         reducible_values ((X, fun t => reducible_values theta t (T_rec n' T0 Ts)) :: theta)
                          v
                          (topen 0 Ts (fvar X type_var))
      )
    );

  reducible_values theta v T := False
.

Hint Transparent lt_measure: core.

Ltac reducibility_definition :=
  repeat step || autorewrite with bsize || unfold "<<", get_measure, closed_value, closed_term in *;
    try solve [ apply right_lex, right_lex, lt_index_step; steps ];
    try solve [ apply right_lex, lt_index_step; steps ];
    try solve [ apply leq_lt_measure; omega ];
    try solve [ apply left_lex; omega ].

Solve Obligations with reducibility_definition.

Fail Next Obligation. (* no more obligations for reducible_values *)

Definition reducible (theta: interpretation) t T : Prop :=
  reduces_to (fun t => reducible_values theta t T) t.

Definition subtype theta T1 T2 :=
  forall v, reducible_values theta v T1 -> reducible_values theta v T2.

Definition open_reducible (tvars: tvar_list) (gamma: context) t T : Prop :=
  forall theta lterms,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma lterms  ->
    support theta = tvars ->
    reducible theta
              (substitute t lterms)
              (substitute T lterms).

Definition open_subtype (tvars: tvar_list) (gamma: context) T1 T2 : Prop :=
  forall theta l,
   valid_interpretation theta ->
   satisfies (reducible_values theta) gamma l ->
   support theta = tvars ->
   subtype theta (substitute T1 l) (substitute T2 l).

Definition open_equivalent (tvars: tvar_list) (gamma: context) t1 t2 : Prop :=
  forall theta l,
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    support theta = tvars ->
    equivalent_terms (substitute t1 l) (substitute t2 l).

Notation "'[' tvars ';' gamma '⊨' t ':' T ']'" := (open_reducible tvars gamma t T)
  (at level 50, t at level 50).

Notation "'[' tvars ';' gamma '⊨' T1 '<:' T2 ']'" := (open_subtype tvars gamma T1 T2)
  (at level 50, T1 at level 50).

Notation "'[' tvars ';' gamma '⊨' t1 '≡' t2 ']'" := (open_equivalent tvars gamma t1 t2)
  (at level 50, t1 at level 50).

Lemma reducibility_rewrite:
  forall theta t T,
    reduces_to (fun t => reducible_values theta t T) t =
    reducible theta t T.
Proof.
  reflexivity.
Qed.

(* see https://github.com/coq/coq/issues/3814 *)
Instance: subrelation eq Basics.impl.
Proof.
  steps.
Qed.

Instance: subrelation eq (Basics.flip Basics.impl).
Proof.
  steps.
Qed.

Ltac simp_red_hyp :=
  match goal with
  | H: _ |- _ => rewrite_strat outermost hints reducible_values in H
  end.

Ltac simp_red_top_level_hyp :=
  match goal with
  | H: _ |- _ => rewrite_strat hints reducible_values in H
  end.

Ltac simp_red_goal := rewrite_strat outermost hints reducible_values.

Ltac simp_red := simp_red_hyp || simp_red_goal.

Ltac simp_red_nat :=
  match goal with
  | H: reducible_values _ _ T_nat |- _ => simp reducible_values in H
  end.
