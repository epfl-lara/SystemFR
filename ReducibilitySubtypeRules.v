Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.TermProperties.
Require Import SystemFR.Sets.
Require Import SystemFR.TermList.
Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.
Require Import SystemFR.Freshness.
Require Import SystemFR.SmallStep.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.StarLemmas.
Require Import SystemFR.StarInversions.
Require Import SystemFR.SmallStepSubstitutions.
Require Import SystemFR.Equivalence.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.StarRelation.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasLists.

Require Import SystemFR.WellFormed.
Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.
Require Import SystemFR.ReducibilityLetRules.
Require Import SystemFR.RedTactics.

Opaque reducible_values.
Opaque Nat.eq_dec.
Opaque makeFresh.

Lemma subtypeExpand:
  forall tvars theta x A B v gamma l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    open_reducible tvars ((x, A) :: gamma) (term_fvar x) B ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta v (substitute A l) ->
    reducible_values theta v (substitute B l).
Proof.
  unfold open_reducible, reducible, reduces_to in *; repeat step.
  unshelve epose proof (H2 theta ((x,v) :: l) _ _ _);
    repeat tac1 || t_values_info2 || t_invert_star.
Qed.

Set Program Mode.

Lemma subtype_arrow2:
  forall tvars theta x f gamma l A B T v,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv T) ->
    ~(f ∈ fv_context gamma) ->
    ~(f ∈ fv A) ->
    ~(f ∈ fv B) ->
    ~(f ∈ fv T) ->
    ~(x = f) ->
    open_reducible tvars ((x, A) :: (f, T) :: gamma)
                   (app (term_fvar f) (term_fvar x))
                   (open 0 B (term_fvar x)) ->
    valid_interpretation theta ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta v (substitute T l) ->
    reducible_values theta v (T_arrow (substitute A l) (substitute B l)).
Proof.
  repeat step || simp_red || rewrite reducibility_rewrite ;
    eauto using red_is_val, values_normalizing with bwf bfv;
    eauto 2 with berased;
    eauto using reducible_values_closed.
  unfold open_reducible in *.
  unshelve epose proof (H8 theta ((x,a) :: (f,v) :: l) _ _ _); tac1.
Qed.

Lemma reducible_ext_pair:
  forall theta A B v,
    is_value v ->
    valid_interpretation theta ->
    reducible theta (pi1 v) A ->
    reducible theta (pi2 v) (T_let (pi1 v) A B) ->
    exists a b,
      v = pp a b /\
      reducible_values theta a A /\
      reducible_values theta b (open 0 B a).
Proof.
  repeat step || unfold reducible, reduces_to in * || t_values_info2 || t_invert_star ||
             t_deterministic_star ||
             match goal with
              | H1: is_value ?v,
                H2: star small_step (pi1 ?t) ?v |- _ =>
                poseNew (Mark H2 "inv pi1");
                unshelve epose proof (star_smallstep_pi1_inv _ v H2 H1 t eq_refl)
              | H1: is_value ?v,
                H2: star small_step (pi2 ?t) ?v |- _ =>
                poseNew (Mark H2 "inv pi2");
                unshelve epose proof (star_smallstep_pi2_inv _ v H2 H1 t eq_refl)
              end.

  eexists; eexists; steps; eauto.
  eapply reducible_val_let2; eauto with values.
  eapply reducible_let_smallstep_values; eauto.
Qed.

Lemma subtype_prod2:
  forall tvars theta gamma l A B T v x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv T) ->
    valid_interpretation theta ->
    support theta = tvars ->
    open_reducible tvars ((x, T) :: gamma) (pi1 (term_fvar x)) A ->
    open_reducible tvars ((x, T) :: gamma) (pi2 (term_fvar x)) (T_let (pi1 (term_fvar x)) A B) ->
    satisfies (reducible_values theta) gamma l ->
    reducible_values theta v (substitute T l) ->
    reducible_values theta v (T_prod (substitute A l) (substitute B l)).
Proof.
  repeat step || simp_red || rewrite reducibility_rewrite ;
    eauto using red_is_val, values_normalizing with bwf bfv;
    t_closer.

  unfold open_reducible in *.

  unshelve epose proof (H5 theta ((x,v) :: l) _ _ _) as HP1;
  unshelve epose proof (H6 theta ((x,v) :: l) _ _ _) as HP2;
    tac1.
  unshelve epose proof reducible_ext_pair _ _ _ _ _ _ HP1 HP2; steps; eauto with values.
  unshelve exists a, b; steps; eauto with berased.
Qed.

Lemma reducible_values_refine_subtype:
  forall theta A p q v,
    wf p 1 ->
    wf q 1 ->
    is_erased_term q ->
    star small_step (open 0 q v) ttrue ->
    reducible_values theta v (T_refine A p) ->
    reducible_values theta v (T_refine A q).
Proof.
  repeat step || simp reducible_values in *.
Qed.

Lemma reducible_values_arrow_subtype:
  forall theta A1 A2 B1 B2 t,
    valid_interpretation theta ->
    (forall a t, reducible_values theta a B1 ->
        reducible_values theta t (open 0 A2 a) ->
        reducible_values theta t (open 0 B2 a)
    ) ->
   (forall t, reducible_values theta t B1 -> reducible_values theta t A1) ->
   reducible_values theta t (T_arrow A1 A2) ->
   reducible_values theta t (T_arrow B1 B2).
Proof.
  repeat step || simp reducible_values in * || unfold reduces_to || t_listutils;
    t_closer.
    match goal with
    | H: forall a, _ |- _ =>
      unshelve epose proof (H a _ _); repeat step || unfold reduces_to in *; eauto
    end.
Qed.

Lemma reducible_arrow_subtype_subst:
  forall theta A1 A2 B1 B2 t l gamma x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    (forall t l,
       satisfies (reducible_values theta) ((x, B1) :: gamma) l ->
       reducible_values theta t (substitute (open 0 A2 (term_fvar x)) l) ->
       reducible_values theta t (substitute (open 0 B2 (term_fvar x)) l)) ->
    (forall t, reducible_values theta t (substitute B1 l) -> reducible_values theta t (substitute A1 l)) ->
    reducible_values theta t (T_arrow (substitute A1 l) (substitute A2 l)) ->
    reducible_values theta t (T_arrow (substitute B1 l) (substitute B2 l)).
Proof.
  intros.
  apply reducible_values_arrow_subtype with (substitute A1 l) (substitute A2 l);
      steps; eauto with berased.
  unshelve epose proof (H5 t0 ((x,a) :: l) _ _); tac1.
Qed.

Lemma reducible_values_prod_subtype:
  forall theta A1 A2 B1 B2 t,
    valid_interpretation theta ->
    (forall a t, reducible_values theta a A1 ->
        reducible_values theta t (open 0 A2 a) ->
        reducible_values theta t (open 0 B2 a)
    ) ->
   (forall t, reducible_values theta t A1 -> reducible_values theta t B1) ->
   reducible_values theta t (T_prod A1 A2) ->
   reducible_values theta t (T_prod B1 B2).
Proof.
  repeat step || simp_red || rewrite reducibility_rewrite in *;
    eauto using reducible_values_exprs.
  eexists; eexists; steps; eauto.
Qed.

Lemma reducible_prod_subtype_subst:
  forall theta A1 A2 B1 B2 t x l gamma,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv A1) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    (forall t l,
       satisfies (reducible_values theta) ((x, A1) :: gamma) l ->
       reducible_values theta t (substitute (open 0 A2 (term_fvar x)) l) ->
       reducible_values theta t (substitute (open 0 B2 (term_fvar x)) l)) ->
    (forall t, reducible_values theta t (substitute A1 l) -> reducible_values theta t (substitute B1 l)) ->
    reducible_values theta t (T_prod (substitute A1 l) (substitute A2 l)) ->
    reducible_values theta t (T_prod (substitute B1 l) (substitute B2 l)).
Proof.
  intros.
  apply reducible_values_prod_subtype with (substitute A1 l) (substitute A2 l);
      steps; eauto with berased.
  unshelve epose proof (H6 t0 ((x,a) :: l) _ _); tac1.
Qed.
