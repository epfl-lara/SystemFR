Require Export SystemFR.Tactics.

Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.FVLemmasLists.
Require Export SystemFR.TOpenTClose.

Lemma close_nothing:
  forall x t k,
    ~(x ∈ pfv t term_var) ->
    close k t x = t.
Proof.
  induction t;
    repeat step || t_equality || list_utils.
Qed.

Lemma close_nothing2:
  forall x t k,
    pfv t term_var = nil ->
    close k t x = t.
Proof.
  intros; apply close_nothing; repeat step || rewrite_any.
Qed.

Lemma open_close3:
  forall t k1 k2 x rep,
    fv rep = nil ->
    wf rep 0 ->
    k1 <> k2 ->
    open k1 (close k2 t x) rep =
    close k2 (open k1 t rep) x.
Proof.
  induction t; repeat step || t_equality || rewrite_any || rewrite close_nothing2 by auto.
Qed.

Lemma substitute_close:
  forall t l tag x k,
    ~(x ∈ support l) ->
    pclosed_mapping l term_var ->
    psubstitute (close k t x) l tag = close k (psubstitute t l tag) x.
Proof.
  induction t;
    repeat step || t_equality || t_lookup || rewrite close_nothing2 by (steps; eauto with fv).
Qed.

Lemma tclose_nothing:
  forall x t k,
    ~(x ∈ pfv t type_var) ->
    tclose k t x = t.
Proof.
  induction t;
    repeat step || t_equality || list_utils.
Qed.

Lemma tclose_nothing2:
  forall x t k,
    pfv t type_var = nil ->
    tclose k t x = t.
Proof.
  intros; apply tclose_nothing; repeat step || rewrite_any.
Qed.

Lemma substitute_tclose:
  forall t l tag x k,
    ~(x ∈ support l) ->
    pclosed_mapping l type_var ->
    psubstitute (tclose k t x) l tag = tclose k (psubstitute t l tag) x.
Proof.
  induction t;
    repeat step || t_equality || t_lookup || rewrite tclose_nothing2 by (steps; eauto with fv).
Qed.

Fixpoint closes k T xs :=
  match xs with
  | nil => T
  | x :: xs => close k (closes (S k) T xs) x
  end.

Lemma is_erased_term_close:
  forall t k x,
    is_erased_term t ->
    is_erased_term (close k t x).
Proof.
  induction t; steps.
Qed.

Lemma is_erased_type_close:
  forall T k x,
    is_erased_type T ->
    is_erased_type (close k T x).
Proof.
  induction T; steps; eauto using is_erased_term_close.
Qed.

#[global]
Hint Resolve is_erased_term_close: erased.
#[global]
Hint Resolve is_erased_type_close: erased.

Lemma is_erased_type_closes:
  forall xs k T,
    is_erased_type T ->
    is_erased_type (closes k T xs).
Proof.
  induction xs; steps; eauto with erased.
Qed.

#[global]
Hint Resolve is_erased_type_closes: erased.

Lemma open_closes:
  forall xs x T v i,
    fv v = nil ->
    wf v 0 ->
    wf T 0 ->
    open (length xs + i) (closes i T (xs ++ x :: nil)) v =
    closes i (psubstitute T ((x, v) :: nil) term_var) xs.
Proof.
  induction xs; repeat step || rewrite open_close; eauto with wf.
  rewrite open_close3; steps; eauto with lia.
  rewrite <- PeanoNat.Nat.add_succ_r.
  rewrite_any; steps.
Qed.

Lemma open_closes_zero:
  forall xs x T v,
    fv v = nil ->
    wf v 0 ->
    wf T 0 ->
    open (length xs) (closes 0 T (xs ++ x :: nil)) v =
    closes 0 (psubstitute T ((x, v) :: nil) term_var) xs.
Proof.
  intros.
  rewrite <- (PeanoNat.Nat.add_0_r (length xs)); eauto using open_closes.
Qed.