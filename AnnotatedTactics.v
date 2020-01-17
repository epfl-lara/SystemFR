Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.AnnotatedTermLemmas.

Lemma open_reducible_same:
  forall tvars gamma t T tvars' gamma' t' T',
    open_reducible tvars gamma t T ->
    tvars = tvars' ->
    gamma = gamma' ->
    t = t' ->
    T = T' ->
    open_reducible tvars' gamma' t' T'.
Proof.
  steps.
Qed.

Ltac erase_open := repeat
  (progress rewrite erase_type_open in * by (steps; eauto with bannot)) ||
  (progress rewrite erase_term_open in * by (steps; eauto with bannot)) ||
  (progress rewrite erase_type_topen in * by (steps; eauto with bannot)) ||
  (progress rewrite erase_term_topen in * by (steps; eauto with bannot)).

Ltac side_conditions :=
  repeat rewrite erased_context_support in *;
  try solve [ t_subset_erase; auto ];
  eauto 2 with fv;
  eauto 2 with wf;
  eauto 2 with wft;
  eauto 2 with btwf;
  eauto 2 with erased;
  try solve [ eapply_anywhere fv_context_support; eauto 2 ].

(*
Ltac side_conditions :=
  repeat
    step || t_fv_erase || t_subset_erase || apply erase_term_wf || apply erase_type_wf ||
    (progress rewrite erase_context_append in * ) ||
    (progress rewrite erased_context_support in * ) || t_erase_open ||
    unshelve eauto with wf wft ||
    unshelve eauto with btwf ||
    unshelve eauto 3 with bfv ||
    unshelve eauto 2 with bfv2 ||
    unshelve eauto 2 with erased;
    try solve [ steps; eauto 2 using subset_transitive with sets ];
    try solve [ repeat t_wf_info; steps ].
*)
