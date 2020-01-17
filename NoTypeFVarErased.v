Require Export SystemFR.TypeErasure.
Require Export SystemFR.TypeErasureLemmas.
Require Export SystemFR.Trees.
Require Export SystemFR.Tactics.
Require Export SystemFR.NoTypeFVar.
Require Export SystemFR.Syntax.


Lemma no_type_fvar_erased:
  forall T vars,
    no_type_fvar T vars ->
    no_type_fvar (erase_type T) vars.
Proof.
  unfold no_type_fvar; steps; eauto with fv.
Qed.
