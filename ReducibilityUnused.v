Require Import Equations.Equations.

Require Import Coq.Strings.String.

Require Export SystemFR.NoTypeFVar.
Require Export SystemFR.ReducibilityRenaming.

Require Import PeanoNat.

Open Scope list_scope.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducible_unused2:
  forall t T (X : nat) (theta : interpretation) (RC : tree -> Prop),
    (X ∈ pfv T type_var -> False) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducible_values theta t T ->
    reducible_values ((X, RC) :: theta) t T.
Proof.
  intros.
  unshelve epose proof (reducible_rename T T t theta ((X,RC) :: theta) (idrel (pfv T type_var)) _ _ _); repeat step || apply equivalent_with_idrel || apply equal_with_idrel || apply equivalent_rc_refl.
Qed.

Lemma reducible_unused3:
  forall t T (X : nat) (theta : interpretation) (RC : tree -> Prop),
    reducible_values ((X, RC) :: theta) t T ->
    (X ∈ pfv T type_var -> False) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    reducible_values theta t T.
Proof.
  intros.
  unshelve epose proof (reducible_rename T T t ((X,RC) :: theta) theta (idrel (pfv T type_var)) _ _ _);    repeat step || apply equivalent_with_idrel2 || apply equal_with_idrel || apply equivalent_rc_refl.
Qed.

Lemma satisfies_unused:
  forall (gamma : list (nat * tree)) lterms (X : nat) (theta : interpretation) RC,
    (X ∈ pfv_context gamma type_var -> False) ->
    valid_interpretation theta ->
    reducibility_candidate RC ->
    satisfies (reducible_values theta) gamma lterms ->
    satisfies (reducible_values ((X, RC) :: theta)) gamma lterms.
Proof.
  induction gamma as [ | [ x T ] gamma' IH ]; destruct lterms;
    repeat step || t_termlist || step_inversion satisfies || list_utils ||
           apply SatCons || apply reducible_unused2 ||
           (rewrite fv_subst_different_tag in * by (steps; eauto with fv)).
Qed.

Lemma reducible_unused_middle:
  forall X RC theta1 theta2 v T,
    valid_interpretation theta1 ->
    valid_interpretation theta2 ->
    reducibility_candidate RC ->
    no_type_fvar T (support theta1) -> (
      reducible_values ((X,RC) :: theta1 ++ theta2) v T <->
      reducible_values ((X,RC) :: theta2) v T
    ).
Proof.
  repeat step.
  - apply reducible_rename with T ((X, RC) :: theta1 ++ theta2) (idrel (pfv T type_var));
      repeat unfold equivalent_with_relation, equivalent_at ||
             step || apply valid_interpretation_append ||
             (progress rewrite swap_idrel in * by steps) ||
             t_idrel_lookup2 || t_lookupor || t_lookup_rewrite || t_lookup ||
             unfold no_type_fvar in * ||
             unshelve eauto with exfalso || exact True;
      eauto using equal_with_idrel;
      eauto using equivalent_rc_refl.

    exists v2; repeat step || rewrite lookupRight || apply lookupNoneSupport; eauto using equivalent_rc_refl.
  - apply reducible_rename with T ((X, RC) :: theta2) (idrel (pfv T type_var));
      repeat step || apply valid_interpretation_append || (rewrite swap_idrel in * by steps) ||
             t_idrel_lookup2 || t_lookupor || t_lookup_rewrite || t_lookup ||
             unfold equivalent_with_relation, equivalent_at || unfold no_type_fvar in * ||
             unshelve eauto with exfalso || exact True;
      eauto using equal_with_idrel;
      eauto using equivalent_rc_refl.

    exists v1; repeat step || rewrite lookupRight || apply lookupNoneSupport; eauto using equivalent_rc_refl.
Qed.

Ltac t_reducible_unused3 :=
  match goal with
  | H: reducible_values ((?X,?RC) :: ?theta) ?v ?T |- reducible_values ?theta' ?v ?T =>
    unify theta theta'; apply reducible_unused3 with X RC
  end.

Lemma reducible_unused_many1:
  forall theta' theta T v,
    no_type_fvar T (support theta') ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    reducible_values (theta' ++ theta) v T ->
    reducible_values theta v T.
Proof.
  induction theta';
    repeat step || (poseNew (Mark 0 "once"); eapply IHtheta') || t_reducible_unused3 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_many2:
  forall theta' theta T v,
    no_type_fvar T (support theta') ->
    valid_interpretation theta ->
    valid_interpretation theta' ->
    reducible_values theta v T ->
    reducible_values (theta' ++ theta) v T.
Proof.
  induction theta';
    repeat step || (poseNew (Mark 0 "once"); eapply IHtheta') || apply reducible_unused2 ||
           apply valid_interpretation_append || apply valid_interpretation_all || unfold sat in * ||
           unfold reducibility_candidate in * || instantiate_any;
    eauto with b_no_type_fvar.
Qed.

Lemma reducible_unused_many:
  forall theta' theta T v,
    no_type_fvar T (support theta') ->
    valid_interpretation theta ->
    valid_interpretation theta' -> (
      reducible_values (theta' ++ theta) v T <->
      reducible_values theta v T
    ).
Proof.
  intuition auto; eauto using reducible_unused_many1, reducible_unused_many2.
Qed.
