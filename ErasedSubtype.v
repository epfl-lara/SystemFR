Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Export SystemFR.ReducibilityOpenEquivalent.

Opaque reducible_values.
Opaque PeanoNat.Nat.eq_dec.
Opaque makeFresh.

Lemma subtype_arrow2:
  forall Θ ρ x f Γ l A B T v,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv T) ->
    ~(f ∈ fv_context Γ) ->
    ~(f ∈ fv A) ->
    ~(f ∈ fv B) ->
    ~(f ∈ fv T) ->
    ~(x = f) ->
    is_erased_type B ->
    [ Θ; (x, A) :: (f, T) :: Γ ⊨
      app (fvar f term_var) (fvar x term_var) : open 0 B (fvar x term_var) ] ->
    valid_interpretation ρ ->
    support ρ = Θ ->
    satisfies (reducible_values ρ) Γ l ->
    [ ρ ⊨ v : substitute T l ]v ->
    [ ρ ⊨ v : T_arrow (substitute A l) (substitute B l) ]v.
Proof.
  repeat step || simp_red || rewrite reducibility_rewrite ;
    eauto using red_is_val, values_normalizing with wf fv;
    eauto 3 with erased;
    eauto using reducible_values_closed.
  unfold open_reducible in *.
  unshelve epose proof (H9 ρ ((x,a) :: (f,v) :: l) _ _ _);
    repeat step || list_utils || apply SatCons || t_substitutions;
    eauto with fv wf erased twf.
Qed.

Lemma reducible_ext_pair:
  forall ρ A B v,
    cbv_value v ->
    valid_interpretation ρ ->
    [ ρ ⊨ pi1 v : A ] ->
    [ ρ ⊨ pi2 v : open 0 B (pi1 v) ] ->
    is_erased_type B ->
    wf B 1 ->
    pfv B term_var = nil ->
    exists a b,
      v = pp a b /\
      [ ρ ⊨ a : A ]v /\
      [ ρ ⊨ b : open 0 B a ]v.
Proof.
  repeat step || unfold reduces_to in * || t_values_info2 || t_invert_star ||
             t_deterministic_star ||
             match goal with
              | H1: cbv_value ?v,
                H2: pi1 ?t ~>* ?v |- _ =>
                poseNew (Mark H2 "inv pi1");
                unshelve epose proof (star_smallstep_pi1_inv _ v H2 H1 t eq_refl)
              | H1: cbv_value ?v,
                H2: pi2 ?t ~>* ?v |- _ =>
                poseNew (Mark H2 "inv pi2");
                unshelve epose proof (star_smallstep_pi2_inv _ v H2 H1 t eq_refl)
              end.

  eexists; eexists; steps; eauto.
  eapply reducibility_values_ltr; eauto; repeat step || list_utils;
    eauto with wf;
    eauto with fv;
    eauto with erased.
Qed.

Lemma subtype_prod2:
  forall ρ Γ l A B T v x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A) ->
    ~(x ∈ fv B) ->
    ~(x ∈ fv T) ->
    valid_interpretation ρ ->
    [ support ρ; (x, T) :: Γ ⊨ pi1 (fvar x term_var) : A ] ->
    [ support ρ; (x, T) :: Γ ⊨ pi2 (fvar x term_var) : open 0 B (pi1 (fvar x term_var)) ] ->
    satisfies (reducible_values ρ) Γ l ->
    is_erased_type B ->
    wf B 1 ->
    subset (fv B) (support Γ) ->
    [ ρ ⊨ v : substitute T l ]v ->
    [ ρ ⊨ v : T_prod (substitute A l) (substitute B l) ]v.
Proof.
  repeat step || simp_red || rewrite reducibility_rewrite ;
    eauto using red_is_val, values_normalizing with wf fv;
    t_closer.

  unfold open_reducible in *.

  unshelve epose proof (H4 ρ ((x,v) :: l) _ _ _) as HP1;
  unshelve epose proof (H5 ρ ((x,v) :: l) _ _ _) as HP2;
    repeat step || list_utils || apply SatCons || t_substitutions;
    eauto with fv wf erased twf.
  unshelve epose proof reducible_ext_pair _ _ _ _ _ _ HP1 HP2 _ _ _; steps;
    eauto with values;
    eauto with fv;
    try solve [ unshelve eauto with wf; auto ].
  unshelve exists a, b; steps; eauto with erased wf fv.
Qed.

Lemma reducible_values_refine_subtype:
  forall ρ A p q v,
    wf p 1 ->
    wf q 1 ->
    is_erased_term q ->
    pfv q term_var = nil ->
    open 0 q v ~>* ttrue ->
    [ ρ ⊨ v : T_refine A p ]v ->
    [ ρ ⊨ v : T_refine A q ]v.
Proof.
  repeat step || simp_red.
Qed.

Lemma reducible_values_arrow_subtype:
  forall ρ A1 A2 B1 B2 v,
    valid_interpretation ρ ->
    (forall a v, [ ρ ⊨ a : B1 ]v ->
        [ ρ ⊨ v : open 0 A2 a ]v ->
        [ ρ ⊨ v : open 0 B2 a ]v
    ) ->
   (forall v, [ ρ ⊨ v : B1 ]v -> [ ρ ⊨ v : A1 ]v) ->
   is_erased_type B2 ->
   [ ρ ⊨ v : T_arrow A1 A2 ]v ->
   [ ρ ⊨ v : T_arrow B1 B2 ]v.
Proof.
  repeat step || simp_red || unfold reduces_to || list_utils;
    t_closer.
    match goal with
    | H: forall a, _ |- _ =>
      unshelve epose proof (H a _ _ _ _); repeat step || unfold reduces_to in *; eauto
    end.
Qed.

Lemma reducible_arrow_subtype_subst:
  forall ρ A1 A2 B1 B2 v l Γ x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    (forall v l,
       satisfies (reducible_values ρ) ((x, B1) :: Γ) l ->
       [ ρ ⊨ v : substitute (open 0 A2 (fvar x term_var)) l ]v ->
       [ ρ ⊨ v : substitute (open 0 B2 (fvar x term_var)) l ]v) ->
    (forall v, [ ρ ⊨ v : substitute B1 l ]v -> [ ρ ⊨ v : substitute A1 l ]v) ->
    is_erased_type B2 ->
    [ ρ ⊨ v : T_arrow (substitute A1 l) (substitute A2 l) ]v ->
    [ ρ ⊨ v : T_arrow (substitute B1 l) (substitute B2 l) ]v.
Proof.
  intros.
  apply reducible_values_arrow_subtype with (substitute A1 l) (substitute A2 l);
      steps; eauto with erased.
  unshelve epose proof (H5 v0 ((x,a) :: l) _ _);
    repeat step || list_utils || apply SatCons || t_substitutions;
    eauto with fv wf erased twf.
Qed.

Lemma reducible_values_prod_subtype:
  forall ρ A1 A2 B1 B2 v,
    valid_interpretation ρ ->
    (forall a v, [ ρ ⊨ a : A1 ]v ->
        [ ρ ⊨ v : open 0 A2 a ]v ->
        [ ρ ⊨ v : open 0 B2 a ]v
    ) ->
   (forall v, [ ρ ⊨ v : A1 ]v -> [ ρ ⊨ v : B1 ]v) ->
   is_erased_type B2 ->
   [ ρ ⊨ v : T_prod A1 A2 ]v ->
   [ ρ ⊨ v : T_prod B1 B2 ]v.
Proof.
  repeat step || simp_red || rewrite reducibility_rewrite in *;
    eauto using reducible_values_exprs.
  eexists; eexists; steps; eauto.
Qed.

Lemma reducible_prod_subtype_subst:
  forall ρ A1 A2 B1 B2 v x l Γ,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv A1) ->
    ~(x ∈ fv B1) ->
    ~(x ∈ fv A2) ->
    ~(x ∈ fv B2) ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ l ->
    (forall v l,
       satisfies (reducible_values ρ) ((x, A1) :: Γ) l ->
       [ ρ ⊨ v : substitute (open 0 A2 (fvar x term_var)) l ]v ->
       [ ρ ⊨ v : substitute (open 0 B2 (fvar x term_var)) l ]v) ->
    (forall v, [ ρ ⊨ v : substitute A1 l ]v -> [ ρ ⊨ v : substitute B1 l ]v) ->
    is_erased_type B2 ->
    [ ρ ⊨ v : T_prod (substitute A1 l) (substitute A2 l) ]v ->
    [ ρ ⊨ v : T_prod (substitute B1 l) (substitute B2 l) ]v.
Proof.
  intros.
  apply reducible_values_prod_subtype with (substitute A1 l) (substitute A2 l);
      steps; eauto with erased.
  unshelve epose proof (H6 v0 ((x,a) :: l) _ _);
    repeat step || list_utils || apply SatCons || t_substitutions;
    t_closer;
    eauto with twf.
Qed.
