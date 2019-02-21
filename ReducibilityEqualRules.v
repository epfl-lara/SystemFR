Require Import Equations.Equations.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Termination.Syntax.
Require Import Termination.Tactics.
Require Import Termination.TermProperties.
Require Import Termination.Sets.
Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Freshness.
Require Import Termination.SmallStep.
Require Import Termination.StarLemmas.
Require Import Termination.StarInversions.
Require Import Termination.SmallStepSubstitutions.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.Equivalence.
Require Import Termination.EquivalenceLemmas.
Require Import Termination.SubstitutionErase.
Require Import Termination.TreeLists.
Require Import Termination.TermListReducible.

Require Import Termination.TermList.
Require Import Termination.TermListLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasLists.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasLists.

Require Import Termination.ReducibilityCandidate.
Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducibility_equivalent_weaken:
  forall theta (gamma : context) (x : nat) T u v l,
    subset (fv u) (support gamma) ->
    subset (fv v) (support gamma) ->
    (forall l,
        satisfies (reducible_values theta) gamma l -> equivalent (substitute u l) (substitute v l)) ->
    satisfies (reducible_values theta) ((x, T) :: gamma) l ->
    equivalent (substitute u l) (substitute v l).
Proof.
  intros.
  unfold open_reducible, subset in *; repeat step || step_inversion satisfies || tac1.
Qed.

Lemma equivalent_error:
  forall tvars theta gamma t T l,
    open_reducible tvars gamma t T ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    support theta = tvars ->
    equivalent notype_err (substitute t l) ->
    False.
Proof.
  repeat step || t_instantiate_sat2 || unfold reducible, reduces_to, equivalent in *;
    eauto using star_smallstep_err, red_is_val.
Qed.

Lemma equivalent_split_bool:
  forall tvars theta (gamma1 gamma2 : context) b t t' x l,
    ~(x ∈ fv b) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    subset (fv b) (support gamma2) ->
    open_reducible tvars gamma2 b T_bool ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equal b ttrue) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equal b tfalse) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    satisfies (reducible_values theta) (gamma1 ++ gamma2) l ->
    equivalent (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || simp_red || t_sat_cut || t_instantiate_sat3.
  - unshelve epose proof (H8 (l1 ++ (x,notype_trefl) :: l2) _); tac1.
  - unshelve epose proof (H9 (l1 ++ (x,notype_trefl) :: l2) _); tac1.
Qed.

Lemma equivalent_split_nat:
  forall tvars theta (gamma1 gamma2 : context) n t t' x y l,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(x = y) ->
    subset (fv n) (support gamma2) ->
    open_reducible tvars gamma2 n T_nat ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall l,
       satisfies (reducible_values theta) (gamma1 ++ (x, T_equal n zero) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    (forall l,
       satisfies (reducible_values theta)
                 (gamma1 ++ (x, T_equal n (succ (fvar y term_var))) :: (y, T_nat) :: gamma2)
                 l ->
       equivalent (substitute t l) (substitute t' l)) ->
    satisfies (reducible_values theta) (gamma1 ++ gamma2) l ->
    equivalent (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to;
    repeat step || t_instantiate_sat3 || simp_red || t_sat_cut.
  destruct t'0; steps.

  - unshelve epose proof (H14 (l1 ++ (x,notype_trefl) :: l2) _); tac1.
  - unshelve epose proof (H15 (l1 ++ (x,notype_trefl) :: (y, t'0) :: l2) _); tac1.
Qed.

Lemma equivalent_pair_eta:
  forall tvars theta (gamma : context) t A B l,
    valid_interpretation theta ->
    open_reducible tvars gamma t (T_prod A B) ->
    support theta = tvars ->
    satisfies (reducible_values theta) gamma l ->
    equivalent (substitute t l) (pp (pi1 (substitute t l)) (pi2 (substitute t l))).
Proof.
  unfold equivalent, open_reducible, reducible in *;
      repeat step || simp_red || unfold reduces_to in * ||
             t_values_info2 || t_invert_star ||
             t_deterministic_star || apply star_smallstep_pp ||
             t_instantiate_sat3;
      eauto using star_smallstep_trans with smallstep bsteplemmas.
Qed.

Lemma reducible_equivalent_ite:
  forall theta tvars (gamma : context) t1 t2 t3 t x l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv t3) ->
    ~(x ∈ fv t) ->
    valid_interpretation theta ->
    open_reducible tvars gamma t1 T_bool ->
    satisfies (reducible_values theta) gamma l ->
    support theta = tvars ->
    (forall l,
       satisfies (reducible_values theta) ((x, T_equal t1 ttrue) :: gamma) l ->
       equivalent (substitute t2 l) (substitute t l)) ->
    (forall l,
       satisfies (reducible_values theta) ((x, T_equal t1 tfalse) :: gamma) l ->
       equivalent (substitute t3 l) (substitute t l)) ->
    equivalent (ite (substitute t1 l) (substitute t2 l) (substitute t3 l)) (substitute t l).
 Proof.
   unfold open_reducible;
     repeat step || apply equivalent_ite || t_instantiate_sat3 || simp_red ||
            t_deterministic_star || unfold reducible, reduces_to in *.

   - unshelve epose proof (H8 ((x, notype_trefl) :: l) _); tac1.
   - unshelve epose proof (H9 ((x, notype_trefl) :: l) _); tac1.
Qed.

Lemma reducible_equivalent_match:
  forall tvars theta (gamma : context) tn t0 ts t n p l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    open_reducible tvars gamma tn T_nat ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall l,
       satisfies (reducible_values theta) ((p, T_equal tn zero) :: gamma) l ->
       equivalent (substitute t0 l) (substitute t l)) ->
    (forall l,
       satisfies (reducible_values theta)
                 ((p, T_equal tn (succ (fvar n term_var))) :: (n, T_nat) :: gamma)
                 l ->
       equivalent (substitute (open 0 ts (fvar n term_var)) l) (substitute t l)) ->
    satisfies (reducible_values theta) gamma l ->
    equivalent (tmatch (substitute tn l) (substitute t0 l) (substitute ts l)) (substitute t l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || t_instantiate_sat3 || simp_red.
  eapply equivalent_match; eauto; steps.

  - unshelve epose proof (H12 ((p,notype_trefl) :: l) _); tac1.
  - unshelve epose proof (H13 ((p,notype_trefl) :: (n,v') :: l) _); tac1.
Qed.

Lemma reducible_equivalent_rec:
  forall tvars theta (gamma : context) tn t0 ts t n p l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(n ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv t0) ->
    ~(n ∈ fv t) ->
    ~(n = p) ->
    open_reducible tvars gamma tn T_nat ->
    valid_interpretation theta ->
    support theta = tvars ->
    (forall l,
       satisfies (reducible_values theta) ((p, T_equal tn zero) :: gamma) l ->
       equivalent (substitute t0 l) (substitute t l)) ->
    (forall l,
       satisfies (reducible_values theta)
                 ((p, T_equal tn (succ (fvar n term_var))) :: (n, T_nat) :: gamma) l ->
       equivalent
         (substitute
            (open 0
                  (open 1 ts (fvar n term_var))
                  (notype_lambda (notype_rec (fvar n term_var) t0 ts))) l)
         (substitute t l)) ->
    satisfies (reducible_values theta) gamma l ->
    equivalent (notype_rec (substitute tn l) (substitute t0 l) (substitute ts l))
               (substitute t l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || t_instantiate_sat3 || simp_red.
  eapply equivalent_rec; eauto; steps.

  - unshelve epose proof (H13 ((p,notype_trefl) :: l) _); tac1.
  - unshelve epose proof (H14 ((p,notype_trefl) :: (n,v') :: l) _); tac1.
Qed.
