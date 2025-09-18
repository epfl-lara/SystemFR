From Stdlib Require Import List.

Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedEquivalentSplit.
Require Export SystemFR.ErasedEquivalentSplitIte.
Require Export SystemFR.ErasedEquivalentSplitMatch.

Lemma annotated_equivalent_ite:
  forall Θ Γ t1 t2 t3 t x,
    ~(x ∈ fv_context Γ) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv t3) ->
    wf t2 0 ->
    wf t3 0 ->
    subset (fv t2) (support Γ) ->
    subset (fv t3) (support Γ) ->
    [[ Θ; Γ ⊨ t1 : T_bool ]]->
    [[ Θ; (x, T_equiv t1 ttrue) :: Γ ⊨ t2 ≡ t  ]]->
    [[ Θ; (x, T_equiv t1 tfalse) :: Γ ⊨ t3 ≡ t ]] ->
    [[ Θ; Γ ⊨ ite t1 t2 t3 ≡ t ]].
Proof.
  unfold open_equivalent;
    steps.
  apply reducible_equivalent_ite with ρ (erase_context Γ) x;
    steps; side_conditions.
Qed.

Lemma annotated_equivalent_match:
    forall Θ Γ tn t0 ts t n p,
      ~(p ∈ fv_context Γ) ->
      ~(p ∈ fv tn) ->
      ~(p ∈ fv ts) ->
      ~(p ∈ fv t0) ->
      ~(p ∈ fv t) ->
      ~(n ∈ fv_context Γ) ->
      ~(n ∈ fv tn) ->
      ~(n ∈ fv ts) ->
      ~(n ∈ fv t) ->
      ~(n = p) ->
      wf t0 0 ->
      wf ts 1 ->
      subset (fv t0) (support Γ) ->
      subset (fv ts) (support Γ) ->
      is_annotated_term ts ->
      [[ Θ; Γ ⊨ tn : T_nat ]] ->
      [[ Θ; (p, T_equiv tn zero) :: Γ ⊨ t0 ≡ t ]] ->
      [[ Θ; (p, T_equiv tn (succ (fvar n term_var))) :: (n, T_nat) :: Γ ⊨ open 0 ts (fvar n term_var) ≡ t ]] ->
      [[ Θ; Γ ⊨ tmatch tn t0 ts ≡ t ]].
Proof.
  unfold open_equivalent;
    steps.
  apply reducible_equivalent_match with ρ (erase_context Γ) n p;
    repeat step || erase_open; side_conditions.
Qed.

Lemma annotated_equivalent_split_bool:
  forall Θ Γ1 Γ2 b t t' x,
    ~(x ∈ fv_context Γ1) ->
    ~(x ∈ fv_context Γ2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv b) ->
    ~(x ∈ Θ) ->
    subset (fv b) (support Γ2) ->
    [[ Θ; Γ2 ⊨ b : T_bool ]] ->
    [[ Θ; Γ1 ++ (x,T_equiv b ttrue) :: Γ2 ⊨ t ≡ t' ]] ->
    [[ Θ; Γ1 ++ (x,T_equiv b tfalse) :: Γ2 ⊨ t ≡ t' ]] ->
    [[ Θ; Γ1 ++ Γ2 ⊨ t ≡ t' ]].
Proof.
  unfold open_equivalent;
    repeat step.

  apply equivalent_split_bool
    with ρ (erase_context Γ1) (erase_context Γ2) (erase_term b) x;
    repeat step || rewrite erase_context_append in *;
    repeat side_conditions.
Qed.

Lemma annotated_equivalent_split_nat:
  forall Θ Γ1 Γ2 n t t' x y,
    ~(x ∈ fv_context Γ1) ->
    ~(x ∈ fv_context Γ2) ->
    ~(y ∈ fv_context Γ1) ->
    ~(y ∈ fv_context Γ2) ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(x = y) ->
    subset (fv n) (support Γ2) ->
    [[ Θ; Γ2 ⊨ n : T_nat ]] ->
    [[ Θ; Γ1 ++ (x,T_equiv n zero) :: Γ2 ⊨ t ≡ t' ]] ->
    [[ Θ; Γ1 ++ (x,T_equiv n (succ (fvar y term_var))) :: (y, T_nat) :: Γ2 ⊨ t ≡ t' ]] ->
    [[ Θ; Γ1 ++ Γ2 ⊨ t ≡ t' ]].
Proof.
  unfold open_equivalent;
    repeat step.

  apply equivalent_split_nat with ρ (erase_context Γ1) (erase_context Γ2) (erase_term n) x y;
    repeat step || rewrite erase_context_append in *;
    repeat side_conditions.
Qed.

Lemma annotated_equivalent_split_ite:
  forall Θ Γ1 Γ2 b e1 e2 t t' e x y,
    ~(x ∈ fv_context Γ1) ->
    ~(x ∈ support Γ2) ->
    ~(y ∈ fv_context Γ1) ->
    ~(y ∈ fv_context Γ2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(x = y) ->
    ~(y ∈ fv b) ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    (forall z, z ∈ fv b -> z ∈ support Γ1 -> False) ->
    (forall z, z ∈ fv e -> z ∈ support Γ1 -> False) ->
    (forall z, z ∈ fv e1 -> z ∈ support Γ1 -> False) ->
    (forall z, z ∈ fv e2 -> z ∈ support Γ1 -> False) ->
    subset (fv b) (support Γ2) ->
    subset (fv e) (support Γ2) ->
    subset (fv e1) (support Γ2) ->
    subset (fv e2) (support Γ2) ->
    wf b 0 ->
    wf e 0 ->
    wf e1 0 ->
    wf e2 0 ->
    [[ Θ; Γ2 ⊨ b : T_bool ]] ->
    [[ Θ; Γ1 ++ (x, T_equiv e1 e) :: (y, T_equiv b ttrue) :: Γ2 ⊨ t ≡ t' ]] ->
    [[ Θ; Γ1 ++ (x, T_equiv e2 e) :: (y, T_equiv b tfalse) :: Γ2 ⊨ t ≡ t' ]] ->
    [[ Θ; Γ1 ++ ((x, T_equiv (ite b e1 e2) e)  :: Γ2) ⊨ t ≡ t' ]].
Proof.
  unfold open_equivalent;
    repeat step.

  apply equivalent_split_ite
    with ρ (erase_context Γ1) (erase_context Γ2)
         (erase_term b) (erase_term e1) (erase_term e2) (erase_term e) x y;
    repeat step || rewrite erase_context_append in * || apply union_left;
    repeat side_conditions.
Qed.

Lemma annotated_equivalent_split_match:
  forall Θ Γ1 Γ2 n t t' e1 e2 e x y z,
    ~(x ∈ fv_context Γ1) ->
    ~(x ∈ fv_context Γ2) ->
    ~(y ∈ fv_context Γ1) ->
    ~(y ∈ fv_context Γ2) ->
    ~(z ∈ fv_context Γ1) ->
    ~(z ∈ fv_context Γ2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv e1) ->
    ~(x ∈ fv e2) ->
    ~(x ∈ fv e) ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(z ∈ fv e) ->
    ~(z ∈ fv t) ->
    ~(z ∈ fv t') ->
    ~(z ∈ fv n) ->
    ~(z ∈ fv e1) ->
    ~(z ∈ fv e2) ->
    ~(z ∈ fv e) ->
    ~(x ∈ Θ) ->
    ~(y ∈ Θ) ->
    ~(z ∈ Θ) ->
    is_annotated_term e2 ->
    NoDup (x :: y :: z :: nil) ->
    (forall r, r ∈ fv n -> r ∈ support Γ1 -> False) ->
    (forall r, r ∈ fv e -> r ∈ support Γ1 -> False) ->
    (forall r, r ∈ fv e1 -> r ∈ support Γ1 -> False) ->
    (forall r, r ∈ fv e2 -> r ∈ support Γ1 -> False) ->
    subset (fv n) (support Γ2) ->
    subset (fv e) (support Γ2) ->
    subset (fv e1) (support Γ2) ->
    subset (fv e2) (support Γ2) ->
    wf n 0 ->
    wf e 0 ->
    wf e1 0 ->
    wf e2 1 ->
    is_annotated_term e2 ->
    [[ Θ; Γ2 ⊨ n : T_nat ]] ->
    [[ Θ; Γ1 ++ (x, T_equiv e1 e) :: (y, T_equiv n zero) :: Γ2 ⊨ t ≡ t' ]] ->
    [[ Θ; Γ1 ++ (x, T_equiv (open 0 e2 (fvar z term_var)) e) ::
                         (y, T_equiv n (succ (fvar z term_var))) ::
                         (z, T_nat) ::
                         Γ2 ⊨
              t ≡ t' ]] ->
    [[ Θ; Γ1 ++ (x, T_equiv (tmatch n e1 e2) e) :: Γ2 ⊨ t ≡ t' ]].
Proof.
  unfold open_equivalent;
    repeat step.

  apply equivalent_split_match
    with ρ (erase_context Γ1) (erase_context Γ2)
         (erase_term n) (erase_term e1) (erase_term e2) (erase_term e) x y z;
    repeat
      step || rewrite erase_context_append in * || apply union_left || erase_open;
      side_conditions.
Qed.
