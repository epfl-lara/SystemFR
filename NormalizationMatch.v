Require Import PeanoNat.

Require Export SystemFR.NormalizationSing.

Lemma open_nmatch_3: forall Θ Γ T2 T3 t t',
  [ t ⤳* t' ] ->
  [ Θ; Γ ⊨ List_Match t T2 T3 = List_Match t' T2 T3 ].
Proof.
Admitted.

Lemma open_nmatch_nil: forall Θ Γ T2 T3,
  [ Θ; Γ ⊨ List_Match tnil T2 T3 = T2 ].
Proof.
Admitted.

Lemma open_nmatch_1: forall Θ Γ T2 T2' T3 t,
  [ t ⤳* tnil ] ->
  [ Θ; Γ ⊨ T2 = T2' ] ->
  [ Θ; Γ ⊨ List_Match t T2 T3 = T2' ].
Proof.
Admitted.

Lemma open_nmatch_cons: forall Θ Γ T2 T3 t1 t2,
  [ Θ; Γ ⊨ List_Match (tcons t1 t2) T2 T3 = open 0 (open 1 T3 t1) t2 ]. (* FIXME *)
Proof.
Admitted.

(*
Lemma open_normalization:
  forall Θ Γ x T t S S',
    lookup Nat.eq_dec Γ x = Some (T_singleton T t) ->
    [ Θ; Γ ⊨ S = S' ] ->
    ~ x ∈ fv S'.
*)

Lemma open_nmatch_2: forall Θ Γ T2 T3 T3' t t1 t2 x y,
  [ t ⤳* tcons t1 t2 ] ->
  [ Θ; (x, T_singleton T_top t1) :: (y, T_singleton List t2) :: Γ ⊨
    open 0 (open 1 T3 (fvar x term_var)) (fvar y term_var) = T3' ] -> (* FIXME *)
  ~ x ∈ fv T3' ->
  ~ y ∈ fv T3' ->
  [ Θ; Γ ⊨ List_Match t T2 T3 = T3' ].
Proof.
Admitted.



