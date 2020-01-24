Require Import Coq.Strings.String.

Require Export SystemFR.RedTactics.

Opaque reducible_values.
Opaque makeFresh.

Lemma equivalent_weaken:
  forall theta gamma x T u v l,
    subset (fv u) (support gamma) ->
    subset (fv v) (support gamma) ->
    (forall l,
      satisfies (reducible_values theta) gamma l ->
      equivalent_terms (substitute u l) (substitute v l)) ->
    satisfies (reducible_values theta) ((x, T) :: gamma) l ->
    equivalent_terms (substitute u l) (substitute v l).
Proof.
  intros.
    repeat step || step_inversion satisfies || t_substitutions.
Qed.

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
