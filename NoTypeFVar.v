Require Export SystemFR.Tactics.

Require Export SystemFR.Syntax.
Require Export SystemFR.ErasedTermLemmas.
Require Export SystemFR.ListUtils.
Require Export SystemFR.FVLemmas.
Require Export SystemFR.FVLemmasLists.

Definition no_type_fvar T vars :=
  forall X, X ∈ pfv T type_var -> X ∈ vars -> False.

Lemma is_erased_term_no_type_fvar:
  forall t vars,
    is_erased_term t ->
    no_type_fvar t vars.
Proof.
  unfold no_type_fvar; repeat step || rewrite is_erased_term_tfv in *.
Qed.

Lemma no_type_fvar_open:
  forall T vars rep k,
    is_erased_term rep ->
    no_type_fvar T vars ->
    no_type_fvar (open k T rep) vars.
Proof.
  unfold no_type_fvar;
    repeat step || t_fv_open || t_listutils ||
           rewrite is_erased_term_tfv in * by steps; eauto.
Qed.

Lemma no_type_fvar_tail:
  forall T x xs,
    no_type_fvar T (x :: xs) ->
    no_type_fvar T xs.
Proof.
  unfold no_type_fvar; repeat step; eauto.
Qed.

Lemma no_type_fvar_head:
  forall T x xs,
    no_type_fvar T (x :: xs) ->
    x ∈ pfv T type_var ->
    False.
Proof.
  unfold no_type_fvar; repeat step; eauto.
Qed.

Hint Immediate no_type_fvar_head: b_no_type_fvar.
Hint Resolve no_type_fvar_tail: b_no_type_fvar.

Lemma no_type_fvar_in_topen:
  forall T vars k X,
    no_type_fvar T vars ->
    ~(X ∈ vars) ->
    no_type_fvar (topen k T (fvar X type_var)) vars.
Proof.
  unfold no_type_fvar; repeat step || t_fv_open || t_listutils; eauto.
Qed.

Lemma no_type_fvar_append:
  forall T vars1 vars2,
    no_type_fvar T vars1 ->
    no_type_fvar T vars2 ->
    no_type_fvar T (vars1 ++ vars2).
Proof.
  unfold no_type_fvar; repeat step || t_listutils; eauto.
Qed.

Lemma no_type_fvar_subst:
  forall T l vars tag,
    pclosed_mapping l type_var ->
    no_type_fvar T vars ->
    no_type_fvar (psubstitute T l tag) vars.
Proof.
  unfold no_type_fvar; repeat step || eapply_any;
    eauto using pfv_in_subst.
Qed.
