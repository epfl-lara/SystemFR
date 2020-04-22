Require Import Coq.Strings.String.

Require Export SystemFR.TermList.
Require Export SystemFR.ReducibilityMeasure.
Require Export SystemFR.ReducibilityCandidate.

Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.
Require Import Coq.Classes.RelationClasses.

Require Import Psatz.

Definition reduces_to (P: tree -> Prop) (t: tree) :=
  closed_term t /\
  exists v, P v /\ t ~>* v.

Lemma reduces_to_equiv:
  forall (P P': tree -> Prop) t,
    reduces_to P t ->
    (forall v, P v -> P' v) ->
    reduces_to P' t.
Proof.
  unfold reduces_to; repeat step; eauto.
Qed.

Reserved Notation "[ ρ ⊨ v : T ]v" (at level 60, ρ at level 60, v at level 60).
Reserved Notation "[ ρ ⊨ t : T ]"  (at level 60, ρ at level 60, t at level 60).

Equations (noind) reducible_values (ρ: interpretation) (v: tree) (T: tree): Prop
    by wf (get_measure T) lt_measure := {
  reducible_values ρ v (fvar X type_var) :=
    match lookup PeanoNat.Nat.eq_dec ρ X with
    | None => False
    | Some P => P v
    end;

  reducible_values ρ v T_unit := v = uu;

  reducible_values ρ v T_bool := v = ttrue \/ v = tfalse;

  reducible_values ρ v T_nat := is_nat_value v;

  reducible_values ρ v (T_abs T) :=
    closed_value v /\
    exists X,
      ~(X ∈ support ρ) /\
      ~(X ∈ pfv T type_var) /\
      forall RC,
        reducibility_candidate RC ->
        [ (X,RC) :: ρ ⊨ v : topen 0 T (fvar X type_var) ]v;

  reducible_values ρ v (T_arrow A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    forall a (p: is_erased_term a),
      wf a 0 ->
      pfv a term_var = nil ->
      [ ρ ⊨ a : A ]v ->
      [ ρ ⊨ app v a : open 0 B a ];

  reducible_values ρ v (T_prod A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    exists a b (_: is_erased_term a),
      wf a 0 /\
      pfv a term_var = nil /\
      v = pp a b /\
      [ ρ ⊨ a : A ]v /\
      [ ρ ⊨ b : open 0 B a ]v;

  reducible_values ρ v (T_sum A B) :=
    closed_value v /\ (
      (exists v', v = tleft v' /\ [ ρ ⊨ v' : A ]v) \/
      (exists v', v = tright v' /\ [ ρ ⊨ v' : B ]v)
    );

  reducible_values ρ v (T_refine T p) :=
    closed_value v /\
    [ ρ ⊨ v : T ]v /\
    is_erased_term p /\
    wf p 1 /\
    pfv p term_var = nil /\
    open 0 p v ~>* ttrue;

  reducible_values ρ v (T_type_refine T1 T2) :=
    exists (_: is_erased_type T2),
    exists (_: closed_value v),
      [ ρ ⊨ v : T1 ]v /\
      exists p, [ ρ ⊨ p : open 0 T2 v ]v;

  reducible_values ρ v (T_intersection A B) :=
    closed_value v /\
    [ ρ ⊨ v : A ]v /\
    [ ρ ⊨ v : B ]v;

  reducible_values ρ v (T_union A B) :=
    closed_value v /\ (
      [ ρ ⊨ v : A ]v \/
      [ ρ ⊨ v : B ]v
    );

  reducible_values ρ v T_top := closed_value v;

  reducible_values ρ v T_bot := False;

  reducible_values ρ v (T_equiv t1 t2) :=
    v = uu /\
    [ t1 ≡ t2 ];

  reducible_values ρ v (T_forall A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    forall a (p: is_erased_term a),
      wf a 0 ->
      pfv a term_var = nil ->
      [ ρ ⊨ a : A ]v ->
      [ ρ ⊨ v : open 0 B a ]v;

  reducible_values ρ v (T_exists A B) :=
    exists (_: is_erased_type B),
    closed_value v /\
    exists a (_: is_erased_term a),
      wf a 0 /\
      pfv a term_var = nil /\
      [ ρ ⊨ a : A ]v /\
      [ ρ ⊨ v : open 0 B a ]v;

  reducible_values ρ v (T_rec n T0 Ts) :=
    closed_value v /\
    is_erased_term n /\ (
      (n ~>* zero /\ [ ρ ⊨ v : T0 ]v) \/
      (exists n' X (p1: is_nat_value n') (p2: n ~>* succ n'),
         ~(X ∈ pfv T0 type_var) /\
         ~(X ∈ pfv Ts type_var) /\
         ~(X ∈ support ρ) /\
          [ (X, fun t => [ ρ ⊨ t : T_rec n' T0 Ts ]v) :: ρ ⊨ v : topen 0 Ts (fvar X type_var) ]v
      )
    );

  reducible_values _ _ _ := False
}
  where "[ ρ ⊨ v : T ]v" := (reducible_values ρ v T)
  where "[ ρ ⊨ t : T ]" := (reduces_to (fun v => [ ρ ⊨ v : T ]v) t)
.

Hint Transparent lt_measure: core.

Ltac reducibility_definition :=
  repeat step || autorewrite with bsize || unfold "<<", get_measure, closed_value, closed_term in *;
    try solve [ apply right_lex, right_lex, lt_index_step; steps ];
    try solve [ apply right_lex, lt_index_step; steps ];
    try solve [ apply leq_lt_measure; lia ];
    try solve [ apply left_lex; lia ].

Solve Obligations with reducibility_definition.

Fail Next Obligation. (* no more obligations for reducible_values *)

Notation "'[' ρ '⊨' T1 '<:' T2 ']'" := (forall v, [ ρ ⊨ v : T1 ]v -> [ ρ ⊨ v : T2 ]v)
  (at level 60, ρ at level 60, T1 at level 60).

Definition equivalent_types ρ T1 T2 :=
  forall v, [ ρ ⊨ v : T1 ]v <-> [ ρ ⊨ v : T2 ]v.

Notation "'[' ρ ⊨ T1 '=' T2 ']'" := (equivalent_types ρ T1 T2)
  (ρ at level 60, T1 at level 60, T2 at level 60).

Definition open_reducible (Θ: tvar_list) (Γ: context) t T : Prop :=
  forall ρ lterms,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ lterms  ->
    support ρ = Θ ->
    [ ρ ⊨ substitute t lterms : substitute T lterms ].

Definition open_subtype (Θ: tvar_list) (Γ: context) T1 T2 : Prop :=
  forall ρ l,
   valid_interpretation ρ ->
   satisfies (reducible_values ρ) Γ l ->
   support ρ = Θ ->
   [ ρ ⊨ substitute T1 l <: substitute T2 l ].

Definition open_equivalent_types (Θ: tvar_list) (Γ: context) T1 T2 : Prop :=
  forall ρ l,
   valid_interpretation ρ ->
   satisfies (reducible_values ρ) Γ l ->
   support ρ = Θ ->
   [ ρ ⊨ substitute T1 l = substitute T2 l ].

Definition open_equivalent (Θ: tvar_list) (Γ: context) t1 t2 : Prop :=
  forall ρ l,
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    support ρ = Θ ->
    [ substitute t1 l ≡ substitute t2 l ].

Notation "'[' Θ ';' Γ '⊨' t ':' T ']'" := (open_reducible Θ Γ t T)
  (at level 60, Θ at level 60, Γ at level 60, t at level 60).

Notation "'[' Θ ';' Γ '⊨' T1 '<:' T2 ']'" := (open_subtype Θ Γ T1 T2)
  (at level 60, Θ at level 60, Γ at level 60, T1 at level 60).

Notation "'[' Θ ';' Γ '⊨' t1 '≡' t2 ']'" := (open_equivalent Θ Γ t1 t2)
  (at level 60, Θ at level 60, Γ at level 60, t1 at level 60, t2 at level 60).

Notation "'[' Θ ';' Γ '⊨' T1 '=' T2 ']'" :=
  (open_equivalent_types Θ Γ T1 T2)
  (at level 60, Θ at level 60, Γ at level 60, T1 at level 60, T2 at level 60).

Notation "'[' Γ '⊩' t ':' T ']'" :=
  (open_reducible nil Γ t T)
  (Γ at level 60, t at level 60, T at level 60).

Notation "'[' Γ '⊩' T1 '<:' T2 ']'" :=
  (open_subtype nil Γ T1 T2)
  (Γ at level 60, T1 at level 60, T2 at level 60).

Notation "'[' Γ '⊩' T1 '=' T2 ']'" :=
  (open_equivalent_types nil Γ T1 T2)
  (Γ at level 60, T1 at level 60, T2 at level 60).

Notation "'[' Γ '⊩' t1 '≡' t2 ']'" :=
  (open_equivalent nil Γ t1 t2)
  (Γ at level 60, t1 at level 60, t2 at level 60).

Lemma reducibility_rewrite:
  forall ρ t T,
    reduces_to (fun v => [ ρ ⊨ v : T ]v) t =
    [ ρ ⊨ t : T ].
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

Ltac simp_red_top_level_goal := rewrite_strat hints reducible_values.

Ltac simp_red := simp_red_hyp || simp_red_goal.

Ltac simp_red_nat :=
  match goal with
  | H: [ _ ⊨ _ : T_nat ]v |- _ => simp reducible_values in H
  end.
