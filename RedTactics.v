Require Import Coq.Strings.String.

Require Export SystemFR.SubstitutionErase.
Require Export SystemFR.EquivalentStar.
Require Export SystemFR.TermListReducible.
Require Export SystemFR.TermListLemmas.

Opaque reducible_values.

Lemma instantiate_open_reducible:
  forall theta gamma t T lterms,
    open_reducible (support theta) gamma t T ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma lterms ->
    reducible theta
              (psubstitute t lterms term_var)
              (psubstitute T lterms term_var).
Proof.
  unfold open_reducible; steps.
Qed.

Ltac find_smallstep_value :=
  match goal with
  | H: star scbv_step ?t ?v |- exists v, star scbv_step ?t v /\ _ => exists v
  | H: star scbv_step ?t ?v |- exists v, _ /\ star scbv_step ?t v => exists v
  | H: star scbv_step ?t ?v |- exists v, _ /\ star scbv_step ?t v /\ _ => exists v
  | H: star scbv_step ?t ?v |- exists x _, _ /\ _ /\ star scbv_step ?t x /\ _ => exists v
  end.

Ltac find_smallstep_value2 :=
  match goal with
  | H: star scbv_step _ ?v |- exists v, star scbv_step _ v /\ _ => exists v
  | H: star scbv_step _ ?v |- exists x _, _ /\ _ /\ star scbv_step _ x /\ _ => exists v
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
  | H: reducible_values _ ?t (open _ ?T _) |- exists _, reducible_values _ _ (open _ ?T' _) => exists t
  | H: reducible_values _ ?t (open _ ?T _) |- exists _, reducible_values _ _ (open _ ?T' _) => exists t
  end.

Ltac find_reducible_value :=
  match goal with
  | H: reducible_values ?theta ?v (topen 0 ?T _) |-
      exists a _, reducible_values ?theta a (topen 0 ?T _) /\ _ => exists v
  end.

Ltac reducibility_choice :=
  match goal with
  | H: reducible_values ?theta ?v (topen 0 ?T _) |-
      reducible_values ?theta ?v (topen 0 ?T _) \/ _ => left
  | H: reducible_values ?theta ?v (topen 0 ?T _) |-
      _ \/ reducible_values ?theta ?v (topen 0 ?T _) => right
  end.

Ltac t_instantiate_sat2 :=
  match goal with
  | H0: open_reducible (support ?theta) ?gamma ?t ?T,
    H1: valid_interpretation ?theta,
    H2: satisfies (reducible_values ?theta) ?gamma ?lterms
    |- _ =>
      poseNew (Mark (theta, gamma, t, T, lterms) "instantiate_open_reducible");
      unshelve epose proof (instantiate_open_reducible theta gamma t T lterms H0 H1 H2)
  end.

Ltac t_instantiate_sat3 :=
  match goal with
  | H0: forall theta lterms,
      valid_interpretation theta ->
      satisfies (reducible_values theta) ?gamma lterms ->
      support theta = support ?theta0 ->
      _,
    H1: valid_interpretation ?theta0,
    H2: satisfies (reducible_values ?theta0) ?gamma ?lterms0
    |- _ =>
      poseNew (Mark (H0, theta0, gamma, lterms0) "instantiate_open_reducible");
      pose proof (H0 theta0 lterms0 H1 H2 eq_refl)
  end.

Ltac t_instantiate_sat4 :=
  match goal with
  | H0: forall theta lterms,
      valid_interpretation theta ->
      satisfies (reducible_values theta) ?gamma lterms ->
      support theta = support _ ->
      _,
    H1: valid_interpretation ?theta0,
    H2: satisfies (reducible_values ?theta0) ?gamma ?lterms0
    |- _ =>
      poseNew (Mark (H0, theta0, gamma, lterms0) "instantiate_sat4");
      unshelve epose proof (H0 _ _ H1 H2 _)
  end.

Ltac t_instantiate_sat5 :=
  match goal with
  | H0: forall lterms theta,
      valid_interpretation theta ->
      satisfies (reducible_values theta) ?gamma lterms ->
      _,
    H1: valid_interpretation ?theta0,
    H2: satisfies (reducible_values ?theta0) ?gamma ?lterms0
    |- _ =>
      poseNew (Mark (H0, theta0, gamma, lterms0) "instantiate_open_reducible");
      pose proof (H0 lterms0 theta0 H1 H2)
  end.

Ltac t_reduces_to :=
  match goal with
  | H: reduces_to ?P ?t |- reduces_to ?P' ?t => apply (reduces_to_equiv P P' t H)
  end.

Ltac t_reduces_to2 :=
  match goal with
  | H1: reducible_values _ ?a _,
    H2: forall a, _ -> _ -> _ ->
            reducible_values ?theta a _ ->
            reduces_to (fun t => reducible_values ?theta t (open 0 ?T _)) _
      |- reduces_to _ _ =>
    poseNew (Mark (H1,H2) "t_reduces_to2");
    apply reduces_to_equiv with (fun t => reducible_values theta t (open 0 T a))
  end.

Ltac t_reduces_to3 :=
  match goal with
  | H1: reducible_values _ ?a ?A,
    H2: forall a, _ -> _ -> _ ->
            reducible_values ?theta a ?A ->
            reduces_to (fun t => reducible_values ?theta t (open 0 ?T _)) _
      |- reduces_to _ _ =>
    poseNew (Mark (H1,H2) "t_reduces_to2");
    apply reduces_to_equiv with (fun t => reducible_values theta t (open 0 T a))
  end.

Ltac t_instantiate_reducible :=
  match goal with
  | H1: reducible_values _ ?v ?T, H3: forall a, _ |- _ =>
    poseNew (Mark (v, H3) "t_instantiate_reducible");
    unshelve epose proof (H3 v _ _ _ H1)
  | H1: reducible_values _ ?v ?T, H2: forall a, _ -> _ |- _ =>
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
    equivalent_terms (psubstitute t ((x, r) :: l) term_var)
               (psubstitute t' ((x, r) :: l) term_var) ->
    equivalent_terms (psubstitute t l term_var) (psubstitute t' l term_var).
Proof.
  repeat step || t_substitutions.
Qed.

Lemma equivalent_insert:
  forall (t t' : tree) (x : nat) l1 l2 r,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    equivalent_terms (psubstitute t (l1 ++ (x, r) :: l2) term_var)
               (psubstitute t' (l1 ++ (x, r) :: l2) term_var) ->
    equivalent_terms (psubstitute t (l1 ++ l2) term_var) (psubstitute t' (l1 ++ l2) term_var).
Proof.
  repeat step || t_substitutions.
Qed.

Lemma equivalent_insert2:
  forall (t t' : tree) x y l1 l2 rx ry,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    (y ∈ pfv t term_var -> False) ->
    (y ∈ pfv t' term_var -> False) ->
    equivalent_terms (psubstitute t (l1 ++ (x, rx) :: (y, ry) :: l2) term_var)
               (psubstitute t' (l1 ++ (x, rx) :: (y, ry) :: l2) term_var) ->
    equivalent_terms (psubstitute t (l1 ++ l2) term_var) (psubstitute t' (l1 ++ l2) term_var).
Proof.
  repeat step || t_substitutions.
Qed.

Lemma equivalent_cons_succ:
  forall (ts t : tree) (n p : nat) (l : list (nat * tree)) v gamma P,
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    is_nat_value v ->
    satisfies P gamma l ->
    equivalent_terms (psubstitute (open 0 ts (fvar n term_var)) ((p, uu) :: (n, v) :: l) term_var)
               (psubstitute t ((p, uu) :: (n, v) :: l) term_var) ->
    equivalent_terms (open 0 (psubstitute ts l term_var) v) (psubstitute t l term_var).
Proof.
  repeat step || t_substitutions.
Qed.

Lemma equivalent_cons2:
  forall (t0 ts t : tree) (n p : nat) (l : list (nat * tree)) v P gamma,
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv t0) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    is_nat_value v ->
    satisfies P gamma l ->
    equivalent_terms
      (psubstitute
         (open 0 (open 1 ts (fvar n term_var)) (notype_lambda (notype_rec (fvar n term_var) t0 ts)))
         ((p, uu) :: (n, v) :: l) term_var)
      (psubstitute t ((p, uu) :: (n, v) :: l) term_var) ->
    equivalent_terms
      (open 0 (open 1 (psubstitute ts l term_var) v)
            (notype_lambda (notype_rec v (psubstitute t0 l term_var) (psubstitute ts l term_var))))
      (psubstitute t l term_var).
Proof.
  repeat step || t_substitutions.
Qed.

Hint Resolve equivalent_cons: b_equiv_subst.
Hint Resolve equivalent_cons2: b_equiv_subst.
Hint Resolve equivalent_cons_succ: b_equiv_subst.
Hint Resolve equivalent_insert: b_equiv_subst.
Hint Resolve equivalent_insert2: b_equiv_subst.

Ltac t_sat_cons_equal_smallstep :=
  lazymatch goal with
  | H0: forall l, satisfies ?P ((?X, T_equiv ?b ?t) :: ?G) l -> _,
    H1: satisfies ?P ?G ?L,
    H2: star scbv_step (psubstitute ?b ?L term_var) ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 ((X, uu) :: L) _)
  end.

Ltac t_sat_insert_equal_smallstep :=
  lazymatch goal with
  | H0: forall l, satisfies ?P (?G1 ++ (?X, T_equiv ?b ?t) :: ?G2) l -> _,
    H1: satisfies ?P (?G1 ++ ?G2) (?L1 ++ ?L2),
    H2: star scbv_step (psubstitute ?b ?L2 term_var) ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 (L1 ++ (X, uu) :: L2) _)
  end.

Ltac t_sat_cons_equal_succ :=
  lazymatch goal with
  | H0: forall l, satisfies ?P ((?X, T_equiv ?b (succ (fvar ?Y term_var))) :: (?Y, T_nat) :: ?G) l -> _,
    H1: satisfies ?P ?G ?L,
    H2: star scbv_step (psubstitute ?b ?L term_var) (succ ?t) |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 ((X, uu) :: (Y, t) :: L) _)
  end.

Ltac t_sat_insert_equal_succ :=
  lazymatch goal with
  | H0: forall l, satisfies ?P (?G1 ++ (?X, T_equiv ?b (succ (fvar ?Y term_var))) :: (?Y, T_nat) :: ?G2) l -> _,
    H1: satisfies ?P (?G1 ++ ?G2) (?L1 ++ ?L2),
    H2: star scbv_step (psubstitute ?b ?L2 term_var) (succ ?t) |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 (L1 ++ (X, uu) :: (Y, t) :: L2) _)
  end.

Ltac t_sat_add :=
  t_sat_cons_equal_smallstep ||
  t_sat_cons_equal_succ ||
  t_sat_insert_equal_smallstep ||
  t_sat_insert_equal_succ.

