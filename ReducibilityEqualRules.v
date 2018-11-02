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

Require Import Termination.TermList.
Require Import Termination.TermListLemmas.

Require Import Termination.FVLemmas.
Require Import Termination.FVLemmasTermList.

Require Import Termination.WFLemmas.
Require Import Termination.WFLemmasTermList.

Require Import Termination.ReducibilityDefinition.
Require Import Termination.ReducibilityLemmas.
Require Import Termination.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma reducibility_equivalent_weaken:
  forall (gamma : context) (x : nat) T (u v : term) l,
    subset (fv u) (support gamma) ->
    subset (fv v) (support gamma) ->
    (forall l : list (nat * term),
        satisfies reducible_values gamma l -> equivalent (substitute u l) (substitute v l)) ->
    satisfies reducible_values ((x, T) :: gamma) l ->
    equivalent (substitute u l) (substitute v l).
Proof.
  intros.
  unfold open_reducible, subset in *; repeat step || step_inversion satisfies || tac1.
Qed.

Lemma equivalent_error:
  forall gamma t T l,
    open_reducible gamma t T ->
    satisfies reducible_values gamma l ->
    equivalent err (substitute t l) ->
    False.    
Proof.
  unfold equivalent, open_reducible, reducible, reduces_to; repeat step || tt;
    eauto using star_smallstep_err, red_is_val.
Qed.

Lemma equivalent_split_bool:
  forall (gamma1 gamma2 : context) (b t t' : term) x l,
    ~(x ∈ fv b) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    subset (fv b) (support gamma2) ->
    open_reducible gamma2 b T_bool ->
    (forall l : list (nat * term),
       satisfies reducible_values (gamma1 ++ (x, T_equal b ttrue) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    (forall l : list (nat * term),
       satisfies reducible_values (gamma1 ++ (x, T_equal b tfalse) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    satisfies reducible_values (gamma1 ++ gamma2) l ->
    equivalent (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || tt || simp_red || t_sat_cut.
  - unshelve epose proof (H6 (l1 ++ (x,trefl) :: l2) _); tac1.
  - unshelve epose proof (H7 (l1 ++ (x,trefl) :: l2) _); tac1.
Qed.  

Lemma equivalent_split_nat:
  forall (gamma1 gamma2 : context) (n t t' : term) x y l,
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
    open_reducible gamma2 n T_nat ->
    (forall l : list (nat * term),
       satisfies reducible_values (gamma1 ++ (x, T_equal n zero) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    (forall l : list (nat * term),
       satisfies reducible_values (gamma1 ++ (x, T_equal n (succ (fvar y))) :: (y, T_nat) :: gamma2) l ->
       equivalent (substitute t l) (substitute t' l)) ->
    satisfies reducible_values (gamma1 ++ gamma2) l ->
    equivalent (substitute t l) (substitute t' l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || tt || simp_red || t_sat_cut.
  destruct t'0; steps.

  - unshelve epose proof (H12 (l1 ++ (x,trefl) :: l2) _); tac1.
  - unshelve epose proof (H13 (l1 ++ (x,trefl) :: (y, t'0) :: l2) _); tac1.
Qed.  

Lemma equivalent_pair_eta:
  forall (gamma : context) (t : term) A B l,
    open_reducible gamma t (T_prod A B) ->
    satisfies reducible_values gamma l ->
    equivalent (substitute t l) (pp (pi1 (substitute t l)) (pi2 (substitute t l))).
Proof.
  unfold equivalent, open_reducible, reducible in *;
      repeat step || instantiate_any || simp_red || unfold reduces_to in * ||
             t_smallstep_subst || t_values_info2 || t_invert_star || 
             t_deterministic_star || apply star_smallstep_pp ||
             match goal with
              | H1: is_value ?v,
                H2: star small_step (pi1 ?t) ?v |- _ =>
                poseNew (Mark H2 "inv pi1");
                unshelve epose proof (star_smallstep_pi1_inv _ v H2 H1 t eq_refl)
              | H1: is_value ?v,
                H2: star small_step (pi2 ?t) ?v |- _ =>
                poseNew (Mark H2 "inv pi2");
                unshelve epose proof (star_smallstep_pi2_inv _ v H2 H1 t eq_refl)
              end;
      eauto using star_smallstep_trans with smallstep bsteplemmas.
Qed.

Lemma reducible_equivalent_ite:
  forall (gamma : context) (t1 t2 t3 t : term) x l,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv t3) ->
    ~(x ∈ fv t) ->
    satisfies reducible_values gamma l ->
    open_reducible gamma t1 T_bool ->
    (forall l : list (nat * term),
       satisfies reducible_values ((x, T_equal t1 ttrue) :: gamma) l ->
       equivalent (substitute t2 l) (substitute t l)) ->
    (forall l : list (nat * term),
       satisfies reducible_values ((x, T_equal t1 tfalse) :: gamma) l ->
       equivalent (substitute t3 l) (substitute t l)) ->
    equivalent (ite (substitute t1 l) (substitute t2 l) (substitute t3 l)) (substitute t l).
 Proof.
   unfold open_reducible;
     repeat step || apply equivalent_ite || tt || simp_red ||
            t_deterministic_star || unfold reducible, reduces_to in *.

   - unshelve epose proof (H6 ((x,trefl) :: l) _); tac1.
   - unshelve epose proof (H7 ((x,trefl) :: l) _); tac1.
Qed.

Lemma reducible_equivalent_match:
  forall (gamma : context) (tn t0 ts t : term) n p l,
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
    open_reducible gamma tn T_nat ->
    (forall l : list (nat * term),
       satisfies reducible_values ((p, T_equal tn zero) :: gamma) l ->
       equivalent (substitute t0 l) (substitute t l)) ->
    (forall l : list (nat * term),
       satisfies reducible_values ((p, T_equal tn (succ (fvar n))) :: (n, T_nat) :: gamma) l ->
       equivalent (substitute (open 0 ts (fvar n)) l) (substitute t l)) ->
    satisfies reducible_values gamma l ->
    equivalent (tmatch (substitute tn l) (substitute t0 l) (substitute ts l)) (substitute t l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || tt || simp_red.
  eapply equivalent_match; eauto; steps.
  
  - unshelve epose proof (H10 ((p,trefl) :: l) _); tac1.
  - unshelve epose proof (H11 ((p,trefl) :: (n,v') :: l) _); tac1.
Qed.

Lemma reducible_equivalent_rec:
  forall (gamma : context) (tn t0 ts t : term) T n p l,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv t0) ->
    ~(n ∈ fv t) ->
    ~(n ∈ fv T) ->
    ~(n = p) ->
    open_reducible gamma tn T_nat ->
    (forall l : list (nat * term),
       satisfies reducible_values ((p, T_equal tn zero) :: gamma) l ->
       equivalent (substitute t0 l) (substitute t l)) ->
    (forall l : list (nat * term),
       satisfies reducible_values ((p, T_equal tn (succ (fvar n))) :: (n, T_nat) :: gamma) l ->
       equivalent
         (substitute
            (open 0 (open 1 ts (fvar n)) (lambda T_unit (rec T (fvar n) t0 ts))) l)
         (substitute t l)) ->
    satisfies reducible_values gamma l ->
    equivalent (rec (substitute T l) (substitute tn l) (substitute t0 l) (substitute ts l))
               (substitute t l).
Proof.
  unfold open_reducible, reducible, reduces_to; repeat step || tt || simp_red.
  eapply equivalent_rec; eauto; steps.
  
  - unshelve epose proof (H13 ((p,trefl) :: l) _); tac1.
  - unshelve epose proof (H14 ((p,trefl) :: (n,v') :: l) _); tac1.
Qed.
    
