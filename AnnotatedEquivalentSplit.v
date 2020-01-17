Require Import Coq.Lists.List.

Require Export SystemFR.AnnotatedTactics.
Require Export SystemFR.Judgments.
Require Export SystemFR.ErasedEquivalentSplit.
Require Export SystemFR.ErasedEquivalentSplitIte.
Require Export SystemFR.ErasedEquivalentSplitMatch.
Require Export SystemFR.ErasedEquivalentSplitRec.

Lemma annotated_equivalent_ite:
  forall tvars gamma t1 t2 t3 t x,
    ~(x ∈ fv_context gamma) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t1) ->
    ~(x ∈ fv t2) ->
    ~(x ∈ fv t3) ->
    wf t2 0 ->
    wf t3 0 ->
    [[ tvars; gamma ⊨ t1 : T_bool ]]->
    [[ tvars; (x, T_equiv t1 ttrue) :: gamma ⊨ t2 ≡ t  ]]->
    [[ tvars; (x, T_equiv t1 tfalse) :: gamma ⊨ t3 ≡ t ]] ->
    [[ tvars; gamma ⊨ ite t1 t2 t3 ≡ t ]].
Proof.
  unfold annotated_equivalent, equivalent;
    steps.
  apply reducible_equivalent_ite with theta (erase_context gamma) x;
    steps; side_conditions.
Qed.

Lemma annotated_equivalent_match:
    forall tvars gamma tn t0 ts t n p,
      ~(p ∈ fv_context gamma) ->
      ~(p ∈ fv tn) ->
      ~(p ∈ fv ts) ->
      ~(p ∈ fv t0) ->
      ~(p ∈ fv t) ->
      ~(n ∈ fv_context gamma) ->
      ~(n ∈ fv tn) ->
      ~(n ∈ fv ts) ->
      ~(n ∈ fv t) ->
      ~(n = p) ->
      wf t0 0 ->
      wf ts 1 ->
      is_annotated_term ts ->
      [[ tvars; gamma ⊨ tn : T_nat ]] ->
      [[ tvars; (p, T_equiv tn zero) :: gamma ⊨ t0 ≡ t ]] ->
      [[ tvars; (p, T_equiv tn (succ (term_fvar n))) :: (n, T_nat) :: gamma ⊨ open 0 ts (term_fvar n) ≡ t ]] ->
      [[ tvars; gamma ⊨ tmatch tn t0 ts ≡ t ]].
Proof.
  unfold annotated_equivalent, equivalent;
    steps.
  apply reducible_equivalent_match with theta (erase_context gamma) n p;
    repeat step || erase_open; side_conditions.
Qed.

Lemma annotated_equivalent_rec:
  forall tvars gamma T tn t0 ts t n p,
    ~(p ∈ fv_context gamma) ->
    ~(p ∈ fv tn) ->
    ~(p ∈ fv ts) ->
    ~(p ∈ fv t0) ->
    ~(p ∈ fv t) ->
    ~(p ∈ fv T) ->
    ~(n ∈ fv_context gamma) ->
    ~(n ∈ fv ts) ->
    ~(n ∈ fv tn) ->
    ~(n ∈ fv t0) ->
    ~(n ∈ fv t) ->
    ~(n ∈ fv T) ->
    ~(n = p) ->
    ~(n ∈ tvars) ->
    ~(p ∈ tvars) ->
    is_annotated_term ts ->
    wf t0 0 ->
    wf ts 2 ->
    [[ tvars; gamma ⊨ tn : T_nat ]] ->
    [[ tvars; (p, T_equiv tn zero) :: gamma ⊨ t0 ≡ t ]] ->
    [[ tvars;
         (p, T_equiv tn (succ (term_fvar n))) :: (n, T_nat) :: gamma ⊨
         open 0 (open 1 ts (term_fvar n)) (lambda T_unit (rec T (term_fvar n) t0 ts)) ≡ t ]] ->
    [[ tvars; gamma ⊨ rec T tn t0 ts ≡ t ]].
Proof.
  unfold annotated_equivalent, equivalent;
    steps.
  apply reducible_equivalent_rec with theta (erase_context gamma) n p;
    repeat step || erase_open; side_conditions.
Qed.

Lemma annotated_equivalent_split_bool:
  forall tvars gamma1 gamma2 b t t' x,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv b) ->
    ~(x ∈ tvars) ->
    subset (fv b) (support gamma2) ->
    [[ tvars; gamma2 ⊨ b : T_bool ]] ->
    [[ tvars; gamma1 ++ (x,T_equiv b ttrue) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ (x,T_equiv b tfalse) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ gamma2 ⊨ t ≡ t' ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step.

  apply equivalent_split_bool
    with theta (erase_context gamma1) (erase_context gamma2) (erase_term b) x;
    repeat step || rewrite erase_context_append in *;
    repeat side_conditions.
Qed.

Lemma annotated_equivalent_split_nat:
  forall tvars gamma1 gamma2 n t t' x y,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(x = y) ->
    subset (fv n) (support gamma2) ->
    [[ tvars; gamma2 ⊨ n : T_nat ]] ->
    [[ tvars; gamma1 ++ (x,T_equiv n zero) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ (x,T_equiv n (succ (term_fvar y))) :: (y, T_nat) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ gamma2 ⊨ t ≡ t' ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step.

  apply equivalent_split_nat with theta (erase_context gamma1) (erase_context gamma2) (erase_term n) x y;
    repeat step || rewrite erase_context_append in *;
    repeat side_conditions.
Qed.

Lemma annotated_equivalent_split_ite:
  forall tvars gamma1 gamma2 b e1 e2 t t' e x y,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ support gamma2) ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(x = y) ->
    ~(y ∈ fv b) ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    (forall z, z ∈ fv b -> z ∈ support gamma1 -> False) ->
    (forall z, z ∈ fv e -> z ∈ support gamma1 -> False) ->
    (forall z, z ∈ fv e1 -> z ∈ support gamma1 -> False) ->
    (forall z, z ∈ fv e2 -> z ∈ support gamma1 -> False) ->
    subset (fv b) (support gamma2) ->
    subset (fv e) (support gamma2) ->
    subset (fv e1) (support gamma2) ->
    subset (fv e2) (support gamma2) ->
    wf b 0 ->
    wf e 0 ->
    wf e1 0 ->
    wf e2 0 ->
    [[ tvars; gamma2 ⊨ b : T_bool ]] ->
    [[ tvars; gamma1 ++ (x, T_equiv e1 e) :: (y, T_equiv b ttrue) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ (x, T_equiv e2 e) :: (y, T_equiv b tfalse) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ ((x, T_equiv (ite b e1 e2) e)  :: gamma2) ⊨ t ≡ t' ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step.

  apply equivalent_split_ite
    with theta (erase_context gamma1) (erase_context gamma2)
         (erase_term b) (erase_term e1) (erase_term e2) (erase_term e) x y;
    repeat step || rewrite erase_context_append in * || apply union_left;
    repeat side_conditions.
Qed.

Lemma annotated_equivalent_split_match:
  forall tvars gamma1 gamma2 n t t' e1 e2 e x y z,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(z ∈ fv_context gamma1) ->
    ~(z ∈ fv_context gamma2) ->
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
    ~(x ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(z ∈ tvars) ->
    is_annotated_term e2 ->
    NoDup (x :: y :: z :: nil) ->
    (forall r, r ∈ fv n -> r ∈ support gamma1 -> False) ->
    (forall r, r ∈ fv e -> r ∈ support gamma1 -> False) ->
    (forall r, r ∈ fv e1 -> r ∈ support gamma1 -> False) ->
    (forall r, r ∈ fv e2 -> r ∈ support gamma1 -> False) ->
    subset (fv n) (support gamma2) ->
    subset (fv e) (support gamma2) ->
    subset (fv e1) (support gamma2) ->
    subset (fv e2) (support gamma2) ->
    wf n 0 ->
    wf e 0 ->
    wf e1 0 ->
    wf e2 1 ->
    is_annotated_term e2 ->
    [[ tvars; gamma2 ⊨ n : T_nat ]] ->
    [[ tvars; gamma1 ++ (x, T_equiv e1 e) :: (y, T_equiv n zero) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ (x, T_equiv (open 0 e2 (term_fvar z)) e) ::
                         (y, T_equiv n (succ (term_fvar z))) ::
                         (z, T_nat) ::
                         gamma2 ⊨
              t ≡ t' ]] ->
    [[ tvars; gamma1 ++ (x, T_equiv (tmatch n e1 e2) e) :: gamma2 ⊨ t ≡ t' ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step.

  apply equivalent_split_match
    with theta (erase_context gamma1) (erase_context gamma2)
         (erase_term n) (erase_term e1) (erase_term e2) (erase_term e) x y z;
    repeat
      step || rewrite erase_context_append in * || apply union_left || erase_open;
      side_conditions.
Qed.

Lemma annotated_equivalent_split_rec:
  forall tvars gamma1 gamma2 n t t' T e1 e2 e x y z,
    ~(x ∈ fv_context gamma1) ->
    ~(x ∈ fv_context gamma2) ->
    ~(y ∈ fv_context gamma1) ->
    ~(y ∈ fv_context gamma2) ->
    ~(z ∈ fv_context gamma1) ->
    ~(z ∈ fv_context gamma2) ->
    ~(x ∈ fv t) ->
    ~(x ∈ fv t') ->
    ~(x ∈ fv n) ->
    ~(x ∈ fv e1) ->
    ~(x ∈ fv e2) ->
    ~(x ∈ fv e) ->
    ~(x ∈ fv T) ->
    ~(y ∈ fv t) ->
    ~(y ∈ fv t') ->
    ~(y ∈ fv n) ->
    ~(y ∈ fv e1) ->
    ~(y ∈ fv e2) ->
    ~(y ∈ fv e) ->
    ~(y ∈ fv T) ->
    ~(z ∈ fv t) ->
    ~(z ∈ fv t') ->
    ~(z ∈ fv n) ->
    ~(z ∈ fv e1) ->
    ~(z ∈ fv e2) ->
    ~(z ∈ fv e) ->
    ~(z ∈ fv T) ->
    ~(x ∈ tvars) ->
    ~(y ∈ tvars) ->
    ~(z ∈ tvars) ->
    (forall r, r ∈ fv n -> r ∈ support gamma1 -> False) ->
    (forall r, r ∈ fv e -> r ∈ support gamma1 -> False) ->
    (forall r, r ∈ fv e1 -> r ∈ support gamma1 -> False) ->
    (forall r, r ∈ fv e2 -> r ∈ support gamma1 -> False) ->
    subset (fv n) (support gamma2) ->
    subset (fv e) (support gamma2) ->
    subset (fv e1) (support gamma2) ->
    subset (fv e2) (support gamma2) ->
    wf n 0 ->
    wf e 0 ->
    wf e1 0 ->
    wf (erase_term e2) 1 ->
    is_annotated_term e2 ->
    NoDup (x :: y :: z :: nil) ->

    [[ tvars; gamma2 ⊨ n : T_nat ]] ->
    [[ tvars; gamma1 ++ (x, T_equiv e1 e) :: (y, T_equiv n zero) :: gamma2 ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ (x, T_equiv
                               (open 0 (open 1 e2 (term_fvar z))
                                             (lambda T_unit (rec T (term_fvar z) e1 e2)))
                               e) ::
                          (y, T_equiv n (succ (term_fvar z))) ::
                          (z, T_nat) ::
                          gamma2
               ⊨ t ≡ t' ]] ->
    [[ tvars; gamma1 ++ ((x, T_equiv (rec T n e1 e2) e)  :: gamma2) ⊨ t ≡ t' ]].
Proof.
  unfold annotated_reducible, annotated_equivalent, equivalent;
    repeat step.

  apply equivalent_split_rec
    with theta (erase_context gamma1) (erase_context gamma2)
         (erase_term n) (erase_term e1) (erase_term e2) (erase_term e) x y z;
    repeat
      step || rewrite erase_context_append in * || apply union_left || erase_open;
      side_conditions.
Qed.
