Require Import PeanoNat.

Require Export SystemFR.RedTactics.
Require Export SystemFR.ScalaDepSugar.

Opaque reducible_values.

Inductive delta_beta_reduction: context -> tree -> tree -> Prop :=
| DBTrue: forall Γ, delta_beta_reduction Γ ttrue ttrue
| DBFalse: forall Γ, delta_beta_reduction Γ tfalse tfalse
.

(*Notation "'[' Γ ⊨ t1 '⤳' t2 ']'" := (delta_beta_step Γ t1 t2)
  (Γ at level 60, t1 at level 60). *)
Notation "'[' Γ ⊨ t1 '⤳*' t2 ']'" := (delta_beta_reduction Γ t1 t2)
  (Γ at level 60, t1 at level 60).

Lemma delta_beta_obs_equiv:
  forall Θ Γ t1 t2,
    [ Γ ⊨ t1 ⤳* t2 ] ->
    [ Θ; Γ ⊨ t1 ≡ t2 ].
Proof.
Admitted.
