Require Import Coq.Strings.String.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma equivalent_weaken:
  forall theta (gamma : context) (x : nat) T u v l,
    subset (fv u) (support gamma) ->
    subset (fv v) (support gamma) ->
    (forall l,
      satisfies (reducible_values theta) gamma l ->
      equivalent_terms (substitute u l) (substitute v l)) ->
    satisfies (reducible_values theta) ((x, T) :: gamma) l ->
    equivalent_terms (substitute u l) (substitute v l).
Proof.
  intros.
  unfold open_reducible, subset in *;
    repeat step || step_inversion satisfies || tac1.
Qed.

Ltac equivalence_instantiate C :=
  match goal with
  | H: equivalent_terms _ _ |- _ =>
    poseNew (Mark (H) "equivalence_instantiate");
    unshelve epose proof ((proj2 (proj2 (proj2 (proj2 H)))) C _ _)
  end.

Lemma equivalent_error:
  forall tvars theta gamma t T l,
    open_reducible tvars gamma t T ->
    valid_interpretation theta ->
    satisfies (reducible_values theta) gamma l ->
    support theta = tvars ->
    equivalent_terms notype_err (substitute t l) ->
    False.
Proof.
  repeat step || t_instantiate_sat2 || equivalence_instantiate (lvar 0 term_var) || rewrite r_normalizing_err in *.

  unfold reducible, reduces_to, scbv_normalizing, closed_term in *;
    repeat step;
    eauto using red_is_val.
Qed.

(*
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
      eauto using star_trans with smallstep cbvlemmas.
Qed.
 *)
