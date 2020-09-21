Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.TypeErasure.

Notation "'[[' Θ ';' Γ '⊨' t ':' T ']]'" := ([ Θ; erase_context Γ ⊨ erase_term t : erase_type T ])
  (at level 60, Θ at level 60, Γ at level 60, t at level 60).

Notation "'[[' Θ ';' Γ '⊨' T1 '<:' T2 ']]'" :=
  ([ Θ; erase_context Γ ⊨ erase_type T1 <: erase_type T2 ])
  (at level 60, Θ at level 60, Γ at level 60, T1 at level 60).

Notation "'[[' Θ ';' Γ '⊨' t1 '≡' t2 ']]'" :=
  ([ Θ; erase_context Γ ⊨ erase_term t1 ≡ erase_term t2 ])
  (at level 60, Θ at level 60, Γ at level 60, t1 at level 60).
