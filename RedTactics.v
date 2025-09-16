From Stdlib Require Import String.

Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.EquivalentStar.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.TermListLemmas.

Opaque reducible_values.

Lemma instantiate_open_reducible:
  forall ρ Γ t T lterms,
    [ support ρ; Γ ⊨ t : T ] ->
    valid_interpretation ρ ->
    satisfies (reducible_values ρ) Γ lterms ->
    [ ρ ⊨ psubstitute t lterms term_var : psubstitute T lterms term_var ].
Proof.
  unfold open_reducible; steps.
Qed.

Ltac find_smallstep_value :=
  match goal with
  | H: ?t ~>* ?v |- exists v, ?t ~>* v /\ _ => exists v
  | H: ?t ~>* ?v |- exists v, _ /\ ?t ~>* v => exists v
  | H: ?t ~>* ?v |- exists v, _ /\ ?t ~>* v /\ _ => exists v
  | H: ?t ~>* ?v |- exists x _, _ /\ _ /\ ?t ~>* x /\ _ => exists v
  end.

Ltac find_smallstep_value2 :=
  match goal with
  | H: _ ~>* ?v |- exists v, _ ~>* v /\ _ => exists v
  | H: _ ~>* ?v |- exists x _, _ /\ _ /\ _ ~>* x /\ _ => exists v
  end.

Ltac find_exists :=
  match goal with
  | |- exists a b _, pp ?c ?d = pp a b /\ _ => exists c, d
  | |- exists a b _, _ /\ pp ?c ?d = pp a b /\ _ => exists c, d
  | |- exists a b _, _ /\ _ /\ pp ?c ?d = pp a b /\ _ => exists c, d
  | |- (exists x, tleft ?v = tleft x /\ _) \/ _  => left; exists v
  | |- _ \/ (exists x, tright ?v = tright x /\ _)  => right; exists v
  end.

Ltac find_exists_open :=
  match goal with
  | H: [ _ ⊨ ?t : open _ ?T _ ]v |- exists _, [ _ ⊨ _ : open _ ?T' _ ]v => exists t
  | H: [ _ ⊨ ?t : open _ ?T _ ]v |- exists _, [ _ ⊨ _ : open _ ?T' _ ]v => exists t
  end.

Ltac find_reducible_value :=
  match goal with
  | H: [ ?ρ ⊨ ?v : topen 0 ?T _ ]v |-
      exists a _, [ ?ρ ⊨ a : topen 0 ?T _ ]v /\ _ => exists v
  end.

Ltac reducibility_choice :=
  match goal with
  | H: [ ?ρ ⊨ ?v : topen 0 ?T _ ]v |-
      [ ?ρ ⊨ ?v : topen 0 ?T _ ]v \/ _ => left
  | H: [ ?ρ ⊨ ?v : topen 0 ?T _ ]v |-
      _ \/ [ ?ρ ⊨ ?v : topen 0 ?T _ ]v => right
  end.

Ltac t_instantiate_sat2 :=
  match goal with
  | H0: [ support ?ρ; ?Γ ⊨ ?t : ?T ],
    H1: valid_interpretation ?ρ,
    H2: satisfies (reducible_values ?ρ) ?Γ ?lterms
    |- _ =>
      poseNew (Mark (ρ, Γ, t, T, lterms) "instantiate_open_reducible");
      unshelve epose proof (instantiate_open_reducible ρ Γ t T lterms H0 H1 H2)
  end.

Ltac t_instantiate_sat3 :=
  match goal with
  | H0: forall ρ lterms,
      valid_interpretation ρ ->
      satisfies (reducible_values ρ) ?Γ lterms ->
      support ρ = support ?ρ0 ->
      _,
    H1: valid_interpretation ?ρ0,
    H2: satisfies (reducible_values ?ρ0) ?Γ ?lterms0
    |- _ =>
      poseNew (Mark (H0, ρ0, Γ, lterms0) "instantiate_open_reducible");
      pose proof (H0 ρ0 lterms0 H1 H2 eq_refl)
  end.

Ltac t_instantiate_sat3_nil :=
  match goal with
  | H0: forall theta lterms,
      valid_interpretation theta ->
      satisfies (reducible_values theta) ?gamma lterms ->
      support theta = nil ->
      _,
    H2: satisfies (reducible_values ?ρ) ?gamma ?lterms0
    |- _ =>
      poseNew (Mark (H0, ρ, gamma, lterms0) "instantiate_open_reducible");
      unshelve epose proof (H0 ρ lterms0 _ H2 _)
  end.

Ltac t_instantiate_sat4 :=
  match goal with
  | H0: forall ρ lterms,
      valid_interpretation ρ ->
      satisfies (reducible_values ρ) ?Γ lterms ->
      support ρ = support _ ->
      _,
    H1: valid_interpretation ?ρ0,
    H2: satisfies (reducible_values ?ρ0) ?Γ ?lterms0
    |- _ =>
      poseNew (Mark (H0, ρ0, Γ, lterms0) "instantiate_sat4");
      unshelve epose proof (H0 _ _ H1 H2 _)
  end.

Ltac t_reduces_to :=
  match goal with
  | H: reduces_to ?P ?t |- reduces_to ?P' ?t => apply (reduces_to_equiv P P' t H)
  end.

Ltac t_reduces_to2 :=
  match goal with
  | H1: [ _ ⊨ ?a : _ ]v,
    H2: forall a, _ -> _ -> _ ->
            [ ?ρ ⊨ a : _ ]v ->
            reduces_to (fun t => [ ?ρ ⊨ t : open 0 ?T _ ]v) _
      |- reduces_to _ _ =>
    poseNew (Mark (H1,H2) "t_reduces_to2");
    apply reduces_to_equiv with (fun t => [ ρ ⊨ t : open 0 T a ]v)
  end.

Ltac t_reduces_to3 :=
  match goal with
  | H1: [ _ ⊨ ?a : ?A ]v,
    H2: forall a, _ -> _ -> _ ->
            [ ?ρ ⊨ a : ?A ]v ->
            reduces_to (fun t => [ ?ρ ⊨ t : open 0 ?T _ ]v) _
      |- reduces_to _ _ =>
    poseNew (Mark (H1,H2) "t_reduces_to2");
    apply reduces_to_equiv with (fun t => [ ρ ⊨ t : open 0 T a ]v)
  end.

Ltac t_instantiate_reducible :=
  match goal with
  | H1: [ _ ⊨ ?v : ?T ]v, H3: forall a, _ |- _ =>
    poseNew (Mark (v, H3) "t_instantiate_reducible");
    unshelve epose proof (H3 v _ _ _ H1)
  | H1: [ _ ⊨ ?v : ?T ]v, H2: forall a, _ -> _ |- _ =>
    poseNew (Mark (v, H2) "t_instantiate_reducible");
    pose proof (H2 v H1)
  end.

Ltac t_instantiate_reducible_erased :=
  match goal with
  | H2: is_erased_term ?v, H3: forall a, _ |- _ =>
    poseNew (Mark (v,H2) "t_instantiate_reducible");
    unshelve epose proof (H3 v H2 _ _ _)
  end.

Ltac t_instantiate_rc :=
  match goal with
  | H: reducibility_candidate ?RC, H2: forall R, reducibility_candidate R -> _ |- _ =>
     poseNew (Mark (H,H2) "instantiate_rc");
     pose proof (H2 RC H)
  end.

Lemma equivalent_cons:
  forall (t t' : tree) (x : nat) l r,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    [ psubstitute t ((x, r) :: l) term_var ≡ psubstitute t' ((x, r) :: l) term_var ] ->
    [ psubstitute t l term_var ≡ psubstitute t' l term_var ].
Proof.
  repeat step || t_substitutions.
Qed.

Lemma equivalent_insert:
  forall (t t' : tree) (x : nat) l1 l2 r,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    [ psubstitute t (l1 ++ (x, r) :: l2) term_var ≡ psubstitute t' (l1 ++ (x, r) :: l2) term_var ] ->
    [ psubstitute t (l1 ++ l2) term_var ≡ psubstitute t' (l1 ++ l2) term_var ].
Proof.
  repeat step || t_substitutions.
Qed.

Lemma equivalent_insert2:
  forall (t t' : tree) x y l1 l2 rx ry,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    (y ∈ pfv t term_var -> False) ->
    (y ∈ pfv t' term_var -> False) ->
    [ psubstitute t (l1 ++ (x, rx) :: (y, ry) :: l2) term_var ≡
      psubstitute t' (l1 ++ (x, rx) :: (y, ry) :: l2) term_var ] ->
    [ psubstitute t (l1 ++ l2) term_var ≡ psubstitute t' (l1 ++ l2) term_var ].
Proof.
  repeat step || t_substitutions.
Qed.

Lemma equivalent_cons_succ:
  forall (ts t : tree) (n p : nat) (l : list (nat * tree)) v Γ P,
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    is_nat_value v ->
    satisfies P Γ l ->
    [ psubstitute (open 0 ts (fvar n term_var)) ((p, uu) :: (n, v) :: l) term_var ≡
      psubstitute t ((p, uu) :: (n, v) :: l) term_var ] ->
    [ open 0 (psubstitute ts l term_var) v ≡ psubstitute t l term_var ].
Proof.
  repeat step || t_substitutions.
Qed.

#[export]
Hint Resolve equivalent_cons: b_equiv_subst.
#[export]
Hint Resolve equivalent_cons_succ: b_equiv_subst.
#[export]
Hint Resolve equivalent_insert: b_equiv_subst.
#[export]
Hint Resolve equivalent_insert2: b_equiv_subst.

Ltac t_sat_cons_equal_smallstep :=
  lazymatch goal with
  | H0: forall l, satisfies ?P ((?X, T_equiv ?b ?t) :: ?G) l -> _,
    H1: satisfies ?P ?G ?L,
    H2: psubstitute ?b ?L term_var ~>* ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 ((X, uu) :: L) _)
  end.

Ltac t_sat_insert_equal_smallstep :=
  lazymatch goal with
  | H0: forall l, satisfies ?P (?G1 ++ (?X, T_equiv ?b ?t) :: ?G2) l -> _,
    H1: satisfies ?P (?G1 ++ ?G2) (?L1 ++ ?L2),
    H2: psubstitute ?b ?L2 term_var ~>* ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 (L1 ++ (X, uu) :: L2) _)
  end.

Ltac t_sat_cons_equal_succ :=
  lazymatch goal with
  | H0: forall l, satisfies ?P ((?X, T_equiv ?b (succ (fvar ?Y term_var))) :: (?Y, T_nat) :: ?G) l -> _,
    H1: satisfies ?P ?G ?L,
    H2: psubstitute ?b ?L term_var ~>* succ ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 ((X, uu) :: (Y, t) :: L) _)
  end.

Ltac t_sat_insert_equal_succ :=
  lazymatch goal with
  | H0: forall l, satisfies ?P (?G1 ++ (?X, T_equiv ?b (succ (fvar ?Y term_var))) :: (?Y, T_nat) :: ?G2) l -> _,
    H1: satisfies ?P (?G1 ++ ?G2) (?L1 ++ ?L2),
    H2: psubstitute ?b ?L2 term_var ~>* succ ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 (L1 ++ (X, uu) :: (Y, t) :: L2) _)
  end.

Ltac t_sat_add :=
  t_sat_cons_equal_smallstep ||
  t_sat_cons_equal_succ ||
  t_sat_insert_equal_smallstep ||
  t_sat_insert_equal_succ.
