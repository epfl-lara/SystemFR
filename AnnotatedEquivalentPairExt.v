Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.RedTactics.
Require Export SystemFR.EquivalentContext.

Opaque reducible_values.

Lemma annotated_equivalent_pair_ext:
  forall tvars gamma t A B,
    is_annotated_term t ->
    wf t 0 ->
    [[ tvars; gamma ⊨ t: T_prod A B ]] ->
    [[ tvars; gamma ⊨ t ≡ pp (pi1 t) (pi2 t) ]].
Proof.
  unfold annotated_reducible, open_reducible, reducible, reduces_to,
         annotated_equivalent, open_equivalent;
    repeat step || t_instantiate_sat3 || simp_red.

  apply equivalent_trans with (pp a b).
  - equivalent_star; t_closer.
  - apply equivalent_trans with (pp (pi1 (psubstitute (erase_term t) l term_var) ) b).
    + unshelve epose proof (equivalent_context (pp (lvar 0 term_var) b) a (pi1 (psubstitute (erase_term t) l term_var)) _ _ _ _);
        repeat step || rewrite (open_none b) in * by t_closer;
        t_closer.
      apply equivalent_sym;
        try solve [ equivalent_star; t_closer ].
    + unshelve epose proof (equivalent_context (pp (pi1 (psubstitute (erase_term t) l term_var)) (lvar 0 term_var))
        b (pi2 (psubstitute (erase_term t) l term_var)) _ _ _ _);
        repeat step || list_utils || rewrite open_none in * by t_closer;
        t_closer.
      apply equivalent_sym;
        try solve [ equivalent_star; t_closer ].
Qed.
