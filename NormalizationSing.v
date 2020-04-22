Require Import PeanoNat.

Require Export SystemFR.ReducibilityDefinition.
Require Export SystemFR.TypeSugar2.

Inductive beta_reduce: tree -> tree -> Prop :=
.

Notation "'[' t1 '⤳' t2 ']'" := (beta_reduce t1 t2)
  (t1 at level 60).
Notation "'[' t1 '⤳*' t2 ']'" := (star beta_reduce t1 t2)
  (t1 at level 60).

Lemma beta_reduce_equiv:
  forall Θ Γ t1 t2,
    [ t1 ⤳* t2 ] ->
    [ Θ; Γ ⊨ t1 ≡ t2 ].
Proof.
Admitted.

Lemma open_reduce_singleton:
  forall Θ Γ T t t',
    [ t ⤳* t' ] ->
    [ Θ; Γ ⊨ tsingleton T t = tsingleton T t' ].
Proof.
Admitted.

Lemma open_ndelta:
  forall Θ Γ T t x S,
    lookup Nat.eq_dec Γ x = Some (tsingleton T t) ->
    [ Θ; Γ ⊨ S = substitute S ((x, t) :: nil) ].
Proof.
  unfold open_equivalent_types; steps.
Admitted.

Definition remove (Γ: context) (x: nat) : context.
Admitted.

Lemma open_ndelta2:
  forall Θ Γ T t x S S',
    lookup Nat.eq_dec Γ x = Some (tsingleton T t) ->
    [ Θ; remove Γ x ⊨ substitute S ((x, t) :: nil) = S' ] ->
    [ Θ; Γ ⊨ S = S' ].
Proof.
Admitted.

Lemma open_nsing:
  forall Θ Γ T T' t t',
    [ t ⤳* t' ] ->
    [ Θ; Γ ⊨ t' : T' ] ->
    [ Θ; Γ ⊨ tsingleton T t = T' ].
Proof.
Admitted.
