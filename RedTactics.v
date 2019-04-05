Require Import Coq.Strings.String.

Require Import SystemFR.Syntax.
Require Import SystemFR.Tactics.
Require Import SystemFR.Freshness.
Require Import SystemFR.ListUtils.
Require Import SystemFR.SubstitutionLemmas.
Require Import SystemFR.TermList.
Require Import SystemFR.TermListLemmas.
Require Import SystemFR.AssocList.
Require Import SystemFR.EquivalenceLemmas.
Require Import SystemFR.SubstitutionErase.
Require Import SystemFR.TreeLists.
Require Import SystemFR.TermListReducible.
Require Import SystemFR.ErasedTermLemmas.
Require Import SystemFR.StarRelation.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Sets.
Require Import SystemFR.Equivalence.
Require Import SystemFR.SubstitutionLemmas.

Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasEval.
Require Import SystemFR.FVLemmasLists.


Require Import SystemFR.WFLemmas.
Require Import SystemFR.WFLemmasEval.
Require Import SystemFR.WFLemmasLists.

Require Import SystemFR.ReducibilityCandidate.
Require Import SystemFR.ReducibilityDefinition.
Require Import SystemFR.ReducibilityLemmas.

Opaque reducible_values.

Ltac t_rewrite :=
  repeat step || t_listutils || t_fv_open || finisher;
    eauto with bwf;
    eauto with btwf;
    eauto with bfv;
    eauto with b_cmap bfv.

Ltac t_closing :=
  unfold closed_value, closed_term in *; repeat step || t_listutils;
    eauto with berased;
    eauto with bwf;
    eauto with bfv;
    eauto with values;
    eauto using is_erased_term_tfv;
    eauto using is_erased_term_twf.

Ltac t_closer := try solve [ t_closing ].

Ltac t_rewriting :=
  (rewrite fv_subst_different_tag by (steps; eauto with bfv)) ||
  (rewrite substitute_nothing2 in * by t_rewrite) ||
  (rewrite substitute_open3 in * by t_rewrite) ||
  (rewrite substitute_topen3 in * by t_rewrite) ||
  (rewrite substitute_skip in * by t_rewrite) ||
  (rewrite substitute_open in * by t_rewrite) ||
  (rewrite substitute_topen in * by t_rewrite).

Ltac tac0 :=
  repeat step || t_listutils || finisher || apply SatCons ||
         apply satisfies_insert || t_satisfies_nodup || t_fv_open ||
           t_rewriting ||
           t_closer;
           eauto with b_equiv;
           eauto with bwf bfv;
           eauto with btwf;
           eauto with berased;
           eauto 3 using NoDup_append with sets.

Ltac tac1 := repeat tac0 || simp_red.

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
  | H: star small_step ?t ?v |- exists v, star small_step ?t v /\ _ => exists v
  | H: star small_step ?t ?v |- exists x _, _ /\ _ /\ star small_step ?t x /\ _ => exists v
  end.

Ltac find_smallstep_value2 :=
  match goal with
  | H: star small_step _ ?v |- exists v, star small_step ?t v /\ _ => exists v
  | H: star small_step _ ?v |- exists x _, _ /\ _ /\ star small_step ?t x /\ _ => exists v
  end.

Ltac find_exists :=
  match goal with
  | |- exists a b _, pp ?c ?d = pp a b /\ _ => exists c, d
  | |- exists x, notype_tfold ?v = notype_tfold x /\ _ => exists v
  | |- (exists x, tleft ?v = tleft x /\ _) \/ _  => left; exists v
  | |- _ \/ (exists x, tright ?v = tright x /\ _)  => right; exists v
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

Ltac t_instantiate_reducible :=
  match goal with
  | H1: reducible_values _ ?v ?T, H2: is_erased_term ?v, H3: forall a, _ -> _ -> _ |- _ =>
    poseNew (Mark (v,H3) "t_instantiate_reducible");
    pose proof (H3 v H2 H1)
  | H1: reducible_values _ ?v ?T, H2: forall a, _ -> _ |- _ =>
    poseNew (Mark (v,H2) "t_instantiate_reducible");
    pose proof (H2 v H1)
  end.

Ltac t_instantiate_rc :=
  match goal with
  | H: reducibility_candidate ?RC, H2: forall R, reducibility_candidate R -> _ |- _ =>
     poseNew (Mark (H,H2) "instantiate_rc");
     pose proof (H2 RC H)
  end.

Lemma satisfies_insert_nat_succ:
  forall (theta : interpretation) (gamma1 gamma2 : context) (b : tree) x y
         (l1 l2 : list (nat * tree)) v,
    satisfies (reducible_values theta) (gamma1 ++ gamma2) (l1 ++ l2) ->
    satisfies (reducible_values theta) gamma2 l2 ->
    star small_step (psubstitute b l2 term_var) (succ v) ->
    support gamma1 = support l1 ->
    support gamma2 = support l2 ->
    closed_term (psubstitute b l2 term_var) ->
    subset (pfv b term_var) (support gamma2) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context gamma1 term_var) ->
    ~(x ∈ pfv_context gamma2 term_var) ->
    ~(y ∈ pfv b term_var) ->
    ~(y ∈ pfv_context gamma1 term_var) ->
    ~(y ∈ pfv_context gamma2 term_var) ->
    ~(x = y) ->
    is_nat_value v ->
    satisfies (reducible_values theta)
              (gamma1 ++ (x, T_equal b (succ (fvar y term_var))) :: (y, T_nat) :: gamma2)
              (l1 ++ (x, notype_trefl) :: (y, v) :: l2).
Proof.
  tac1.
Qed.

Hint Resolve satisfies_insert_nat_succ: b_sat.

Lemma satisfies_cons_nat_succ:
  forall (theta : interpretation) gamma (b : tree) x y l v,
    satisfies (reducible_values theta) gamma l ->
    star small_step (psubstitute b l term_var) (succ v) ->
    closed_term (psubstitute b l term_var) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context gamma term_var) ->
    ~(y ∈ pfv b term_var) ->
    ~(y ∈ pfv_context gamma term_var) ->
    ~(x = y) ->
    is_nat_value v ->
    satisfies (reducible_values theta)
              ((x, T_equal b (succ (fvar y term_var))) :: (y, T_nat) :: gamma)
              ((x, notype_trefl) :: (y, v) :: l).
Proof.
  tac1.
Qed.

Hint Resolve satisfies_cons_nat_succ: b_sat.

Lemma satisfies_insert2:
  forall (theta : interpretation) (gamma1 gamma2 : context) (b : tree) (x : nat)
         (l1 l2 : list (nat * tree)) t,
    satisfies (reducible_values theta) (gamma1 ++ gamma2) (l1 ++ l2) ->
    satisfies (reducible_values theta) gamma2 l2 ->
    star small_step (psubstitute b l2 term_var) t ->
    support gamma1 = support l1 ->
    support gamma2 = support l2 ->
    closed_term (psubstitute b l2 term_var) ->
    subset (pfv b term_var) (support gamma2) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context gamma1 term_var) ->
    ~(x ∈ pfv_context gamma2 term_var) ->
    closed_term t ->
    satisfies (reducible_values theta) (gamma1 ++ (x, T_equal b t) :: gamma2)
              (l1 ++ (x, notype_trefl) :: l2).
Proof.
  unfold closed_term; repeat tac1 || rewrite (substitute_nothing5 t) by steps.
Qed.

Hint Resolve satisfies_insert2: b_sat.
Hint Extern 50 => eapply satisfies_insert2; eauto 1; t_closing: b_sat.

Lemma satisfies_insert3:
  forall (theta : interpretation) gamma (b : tree) (x : nat) l t,
    satisfies (reducible_values theta) gamma l ->
    star small_step (psubstitute b l term_var) t ->
    closed_term (psubstitute b l term_var) ->
    ~(x ∈ pfv b term_var) ->
    ~(x ∈ pfv_context gamma term_var) ->
    closed_term t ->
    satisfies (reducible_values theta)
              ((x, T_equal b t) :: gamma)
              ((x, notype_trefl) :: l).
Proof.
  unfold closed_term; repeat tac1 || rewrite (substitute_nothing5 t) by steps.
Qed.

Hint Resolve satisfies_insert3: b_sat.
Hint Extern 50 => eapply satisfies_insert3; eauto; t_closing: b_sat.

Lemma equivalent_cons:
  forall (t t' : tree) (x : nat) l r,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    equivalent (psubstitute t ((x, r) :: l) term_var)
               (psubstitute t' ((x, r) :: l) term_var) ->
    equivalent (psubstitute t l term_var) (psubstitute t' l term_var).
Proof.
  tac1.
Qed.

Lemma equivalent_insert:
  forall (t t' : tree) (x : nat) l1 l2 r,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    equivalent (psubstitute t (l1 ++ (x, r) :: l2) term_var)
               (psubstitute t' (l1 ++ (x, r) :: l2) term_var) ->
    equivalent (psubstitute t (l1 ++ l2) term_var) (psubstitute t' (l1 ++ l2) term_var).
Proof.
  tac1.
Qed.

Lemma equivalent_insert2:
  forall (t t' : tree) x y l1 l2 rx ry,
    (x ∈ pfv t term_var -> False) ->
    (x ∈ pfv t' term_var -> False) ->
    (y ∈ pfv t term_var -> False) ->
    (y ∈ pfv t' term_var -> False) ->
    equivalent (psubstitute t (l1 ++ (x, rx) :: (y, ry) :: l2) term_var)
               (psubstitute t' (l1 ++ (x, rx) :: (y, ry) :: l2) term_var) ->
    equivalent (psubstitute t (l1 ++ l2) term_var) (psubstitute t' (l1 ++ l2) term_var).
Proof.
  tac1.
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
    equivalent (psubstitute (open 0 ts (fvar n term_var)) ((p, notype_trefl) :: (n, v) :: l) term_var)
               (psubstitute t ((p, notype_trefl) :: (n, v) :: l) term_var) ->
    equivalent (open 0 (psubstitute ts l term_var) v) (psubstitute t l term_var).
Proof.
  tac0.
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
    equivalent
      (psubstitute
         (open 0 (open 1 ts (fvar n term_var)) (notype_lambda (notype_rec (fvar n term_var) t0 ts)))
         ((p, notype_trefl) :: (n, v) :: l) term_var)
      (psubstitute t ((p, notype_trefl) :: (n, v) :: l) term_var) ->
    equivalent
      (open 0 (open 1 (psubstitute ts l term_var) v)
            (notype_lambda (notype_rec v (psubstitute t0 l term_var) (psubstitute ts l term_var))))
      (psubstitute t l term_var).
Proof.
  tac0.
Qed.

Hint Resolve equivalent_cons: b_equiv_subst.
Hint Resolve equivalent_cons2: b_equiv_subst.
Hint Resolve equivalent_cons_succ: b_equiv_subst.
Hint Resolve equivalent_insert: b_equiv_subst.
Hint Resolve equivalent_insert2: b_equiv_subst.

Ltac t_sat_cons_equal_smallstep :=
  lazymatch goal with
  | H0: forall l, satisfies ?P ((?X, T_equal ?b ?t) :: ?G) l -> _,
    H1: satisfies ?P ?G ?L,
    H2: star small_step (psubstitute ?b ?L term_var) ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 ((X, notype_trefl) :: L) _)
  end.

Ltac t_sat_insert_equal_smallstep :=
  lazymatch goal with
  | H0: forall l, satisfies ?P (?G1 ++ (?X, T_equal ?b ?t) :: ?G2) l -> _,
    H1: satisfies ?P (?G1 ++ ?G2) (?L1 ++ ?L2),
    H2: star small_step (psubstitute ?b ?L2 term_var) ?t |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 (L1 ++ (X, notype_trefl) :: L2) _)
  end.

Ltac t_sat_cons_equal_succ :=
  lazymatch goal with
  | H0: forall l, satisfies ?P ((?X, T_equal ?b (succ (fvar ?Y term_var))) :: (?Y, T_nat) :: ?G) l -> _,
    H1: satisfies ?P ?G ?L,
    H2: star small_step (psubstitute ?b ?L term_var) (succ ?t) |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 ((X, notype_trefl) :: (Y, t) :: L) _)
  end.

Ltac t_sat_insert_equal_succ :=
  lazymatch goal with
  | H0: forall l, satisfies ?P (?G1 ++ (?X, T_equal ?b (succ (fvar ?Y term_var))) :: (?Y, T_nat) :: ?G2) l -> _,
    H1: satisfies ?P (?G1 ++ ?G2) (?L1 ++ ?L2),
    H2: star small_step (psubstitute ?b ?L2 term_var) (succ ?t) |- _ =>
      poseNew (Mark (X,H0) "t_instantiate_insert");
      unshelve epose proof (H0 (L1 ++ (X, notype_trefl) :: (Y, t) :: L2) _)
  end.

Ltac t_sat_add :=
  t_sat_cons_equal_smallstep ||
  t_sat_cons_equal_succ ||
  t_sat_insert_equal_smallstep ||
  t_sat_insert_equal_succ.

