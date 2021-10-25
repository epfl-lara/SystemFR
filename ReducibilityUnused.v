From Equations Require Import Equations.

Require Import Coq.Strings.String.

Require Export SystemFR.NoTypeFVar.
Require Export SystemFR.ReducibilityRenaming.

Require Import PeanoNat.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_unused2:
  forall v T (X : nat) (ρ : interpretation) RC,
    (X ∈ pfv T type_var -> False) ->
    [ ρ ⊨ v : T ]v ->
    [ (X, RC) :: ρ ⊨ v : T ]v.
Proof.
  intros.
  unshelve epose proof (reducible_rename T T v ρ ((X,RC) :: ρ) (idrel (pfv T type_var)) _ _ _);
    repeat step || apply equivalent_with_idrel || apply equal_with_idrel || apply equivalent_rc_refl.
Qed.

Lemma reducible_unused3:
  forall v T (X : nat) (ρ : interpretation) RC,
    [ (X, RC) :: ρ ⊨ v : T ]v ->
    (X ∈ pfv T type_var -> False) ->
    [ ρ ⊨ v : T ]v.
Proof.
  intros.
  unshelve epose proof (reducible_rename T T v ((X,RC) :: ρ) ρ (idrel (pfv T type_var)) _ _ _);
    repeat step || apply equivalent_with_idrel2 || apply equal_with_idrel || apply equivalent_rc_refl.
Qed.

Lemma satisfies_unused:
  forall (Γ : list (nat * tree)) lterms (X : nat) (ρ : interpretation) RC,
    (X ∈ pfv_context Γ type_var -> False) ->
    satisfies (reducible_values ρ) Γ lterms ->
    satisfies (reducible_values ((X, RC) :: ρ)) Γ lterms.
Proof.
  induction Γ as [ | [ x T ] Γ' IH ]; destruct lterms;
    repeat step || t_termlist || step_inversion satisfies || list_utils ||
           apply SatCons || apply reducible_unused2 ||
           (rewrite fv_subst_different_tag in * by (steps; eauto with fv)).
Qed.

Lemma reducible_unused_middle:
  forall X RC ρ1 ρ2 v T,
    no_type_fvar T (support ρ1) -> (
      [ (X,RC) :: ρ1 ++ ρ2 ⊨ v : T ]v <->
      [ (X,RC) :: ρ2 ⊨ v : T ]v
    ).
Proof.
  repeat step.
  - apply reducible_rename with T ((X, RC) :: ρ1 ++ ρ2) (idrel (pfv T type_var));
      repeat unfold equivalent_with_relation, equivalent_with ||
             step || apply valid_interpretation_append ||
             (progress rewrite swap_idrel in * by steps) ||
             t_idrel_lookup2 || t_lookupor || t_lookup_rewrite || t_lookup ||
             unfold no_type_fvar in * ||
             unshelve eauto with exfalso || exact True;
      eauto using equal_with_idrel;
      eauto using equivalent_rc_refl.

    exists v2; repeat step || rewrite lookupRight || apply lookupNoneSupport; eauto using equivalent_rc_refl.
  - apply reducible_rename with T ((X, RC) :: ρ2) (idrel (pfv T type_var));
      repeat step || apply valid_interpretation_append || (rewrite swap_idrel in * by steps) ||
             t_idrel_lookup2 || t_lookupor || t_lookup_rewrite || t_lookup ||
             unfold equivalent_with_relation, equivalent_with || unfold no_type_fvar in * ||
             unshelve eauto with exfalso || exact True;
      eauto using equal_with_idrel;
      eauto using equivalent_rc_refl.

    exists v1; repeat step || rewrite lookupRight || apply lookupNoneSupport; eauto using equivalent_rc_refl.
Qed.

Ltac t_reducible_unused3 :=
  match goal with
  | H: [ (?X,?RC) :: ?ρ ⊨ ?v : ?T ]v |- [ ?ρ' ⊨ ?v : ?T ]v =>
    unify ρ ρ'; apply reducible_unused3 with X RC
  end.

Lemma reducible_unused_many1:
  forall ρ' ρ T v,
    no_type_fvar T (support ρ') ->
    [ ρ' ++ ρ ⊨ v : T ]v ->
    [ ρ ⊨ v : T ]v.
Proof.
  induction ρ';
    repeat step || (poseNew (Mark 0 "once"); eapply IHρ') || t_reducible_unused3 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_many2:
  forall ρ' ρ T v,
    no_type_fvar T (support ρ') ->
    [ ρ ⊨ v : T ]v ->
    [ ρ' ++ ρ ⊨ v : T ]v.
Proof.
  induction ρ';
    repeat step || (poseNew (Mark 0 "once"); eapply IHρ') || apply reducible_unused2 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_many:
  forall ρ' ρ T v,
    no_type_fvar T (support ρ') -> (
      [ ρ' ++ ρ ⊨ v : T ]v <->
      [ ρ ⊨ v : T ]v
    ).
Proof.
  intuition auto; eauto using reducible_unused_many1, reducible_unused_many2.
Qed.
