Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.TypeErasure.

Definition annotated_reducible tvars gamma t T : Prop :=
  open_reducible tvars (erase_context gamma) (erase_term t) (erase_type T).

Definition annotated_subtype tvars gamma T1 T2 : Prop :=
  open_subtype tvars (erase_context gamma) (erase_type T1) (erase_type T2).

Definition annotated_equivalent tvars gamma t1 t2 : Prop :=
  open_equivalent tvars (erase_context gamma) (erase_term t1) (erase_term t2).

Notation "'[[' tvars ';' gamma '⊨' t ':' T ']]'" := (annotated_reducible tvars gamma t T)
  (at level 50, t at level 50).

Notation "'[[' tvars ';' gamma '⊨' T1 '<:' T2 ']]'" := (annotated_subtype tvars gamma T1 T2)
  (at level 50, T1 at level 50).

Notation "'[[' tvars ';' gamma '⊨' t1 '≡' t2 ']]'" := (annotated_equivalent tvars gamma t1 t2)
  (at level 50, t1 at level 50).
