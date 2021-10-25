From Equations Require Import Equations.
Require Import Equations.Prop.Subterm.

Require Import Psatz.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Export SystemFR.OpenTOpen.
Require Export SystemFR.ReducibilitySubst.
Require Export SystemFR.TOpenTClose.
Require Export SystemFR.NoTypeFVar.
Require Export SystemFR.Polarity.
Require Export SystemFR.EquivalentPairsWithRelation.

Opaque makeFresh.
Opaque PeanoNat.Nat.eq_dec.
Opaque reducible_values.

Lemma polarity_open_aux:
  forall m T pols k rep,
    type_nodes T < m ->
    has_polarities T pols ->
    is_erased_term rep ->
    has_polarities (open k T rep) pols.
Proof.
  induction m; destruct T;
    repeat step || constructor || step_inversion has_polarities;
      eauto with lia;
      eauto with b_polarity.
  exists X; repeat
         step || fv_open || list_utils ||
         (progress rewrite is_erased_term_tfv in * by steps) ||
         (rewrite <- open_topen by (steps; eauto with twf)).

  apply_any; repeat step || autorewrite with bsize; try lia.
Qed.

Lemma polarity_open:
  forall T pols k rep,
    has_polarities T pols ->
    is_erased_term rep ->
    has_polarities (open k T rep) pols.
Proof.
  eauto using polarity_open_aux.
Qed.

Lemma pair_in_list:
  forall X Y (l: list (X*Y)) x y,
    (x,y) ∈ l ->
    x ∈ support l.
Proof.
  induction l; steps; eauto.
Qed.

Lemma support_invert_polarities:
  forall pols, support (invert_polarities pols) = support pols.
Proof.
  induction pols; repeat step || f_equal.
Qed.

Lemma equivalent_pairs_same:
  forall pols pols' rel X X',
    equivalent_pairs_with_relation rel pols pols' eq ->
    lookup PeanoNat.Nat.eq_dec rel X = Some X' ->
    lookup PeanoNat.Nat.eq_dec (swap rel) X' = Some X ->
    ((X, Negative) ∈ pols -> False) ->
    (X', Negative) ∈ pols' ->
    False.
Proof.
  induction pols; destruct pols'; repeat step; eauto.
Qed.

Definition hp_rename_prop T :=
  forall pols T' pols' rel,
    has_polarities T pols ->
    equivalent_pairs_with_relation rel pols pols' eq ->
    equal_with_relation type_var rel T T' ->
    has_polarities T' pols'.

Definition hp_rename_prop_aux n T := type_nodes T = n -> hp_rename_prop T.

Definition hp_rename_until n :=
  forall n', n' < n -> forall T, hp_rename_prop_aux n' T.

#[export]
Hint Unfold hp_rename_prop: u_hprename.
#[export]
Hint Unfold hp_rename_prop_aux: u_hprename.
#[export]
Hint Unfold hp_rename_until: u_hprename.

Lemma has_polarities_rename_fvar:
  forall n x f, hp_rename_prop_aux n (fvar x f).
Proof.
  repeat autounfold with u_hprename.
  repeat step || step_inversion has_polarities.
  force_invert equal_with_relation;
    repeat step;
    try solve [ constructor; eauto with lia; eauto using equivalent_pairs_same ].
Qed.

#[export]
Hint Immediate has_polarities_rename_fvar: b_hp_rename.

Lemma equivalent_with_pairs_invert:
  forall (pols pols' : map nat polarity) (rel : map nat nat),
    equivalent_pairs_with_relation rel pols pols' eq ->
    equivalent_pairs_with_relation rel (invert_polarities pols) (invert_polarities pols') eq.
Proof.
  induction pols; steps.
Qed.

Lemma hp_rename_induct_invert:
  forall T1 T2 n pols pols' rel,
    hp_rename_until n ->
    equivalent_pairs_with_relation rel pols pols' eq ->
    has_polarities T1 (invert_polarities pols) ->
    equal_with_relation type_var rel T1 T2 ->
    type_nodes T1 < n ->
    has_polarities T2 (invert_polarities pols').
Proof.
  repeat autounfold with u_hprename; intros.
  repeat step || eapply_any;
    eauto using equivalent_with_pairs_invert.
Qed.

Lemma hp_rename_induct:
  forall T1 T2 n pols pols' rel,
    hp_rename_until n ->
    equivalent_pairs_with_relation rel pols pols' eq ->
    has_polarities T1 pols ->
    equal_with_relation type_var rel T1 T2 ->
    type_nodes T1 < n ->
    has_polarities T2 pols'.
Proof.
  repeat autounfold with u_hprename; intros.
  repeat step; eauto.
Qed.

Lemma equivalent_with_pairs_cons:
  forall T (pols pols': map nat T) (rel : map nat nat) X Y,
    equivalent_pairs_with_relation rel pols pols' eq ->
    (X ∈ support pols -> False) ->
    (Y ∈ range rel -> False) ->
    equivalent_pairs_with_relation ((X, Y) :: rel) pols pols' eq.
Proof.
  induction pols; destruct pols'; repeat step || t_lookup.
Qed.

Lemma has_polarities_rename_rec:
  forall n k T0 Ts, hp_rename_until n -> hp_rename_prop_aux n (T_rec k T0 Ts).
Proof.
  unfold hp_rename_prop_aux, hp_rename_prop.
  repeat
    step || step_inversion has_polarities || step_inversion equal_with_relation || constructor;
    eauto using hp_rename_induct_invert with lia;
    eauto using hp_rename_induct with lia.

  - exists (makeFresh (pfv Ts' type_var :: support pols' :: range rel :: nil)); steps; try finisher.
    eapply (
        hp_rename_induct _ _ _ _ _
                         ((X, makeFresh (pfv Ts' type_var :: support pols' :: range rel :: nil)) :: rel)); eauto 1;
      repeat step || apply equal_with_relation_topen || finisher || autorewrite with bsize ||
             apply equivalent_with_pairs_cons;
      try lia; try finisher.
Qed.

#[export]
Hint Immediate has_polarities_rename_rec: b_hp_rename.

Lemma strong_induction_aux:
  forall P,
    (forall n, (forall n', n' < n -> P n') -> P n) ->
    forall n, forall n', n' < n -> P n'.
Proof.
  induction n; repeat step; eauto with lia.
Qed.

Lemma strong_induction:
  forall P,
    (forall n, (forall n', n' < n -> P n') -> P n) ->
    forall n, P n.
Proof.
  intros; eapply strong_induction_aux; steps.
Qed.

Lemma has_polarities_rename_aux: forall n T, hp_rename_prop_aux n T.
Proof.
  induction n using strong_induction; destruct T; steps;
    eauto 2 with b_hp_rename;
    try solve [
      unfold hp_rename_prop_aux, hp_rename_prop;
      repeat
        step || step_inversion has_polarities || step_inversion equal_with_relation || constructor;
        eauto using hp_rename_induct with lia;
        eauto using hp_rename_induct_invert with lia
    ].
Qed.

Lemma has_polarities_rename: forall T, hp_rename_prop T.
Proof.
  intros; eapply has_polarities_rename_aux; eauto.
Qed.

Lemma equivalent_with_pairs_refl:
  forall T rel (l: list (nat * T)),
    (forall x, x ∈ support l -> lookup PeanoNat.Nat.eq_dec rel x = Some x) ->
    (forall x, x ∈ support l -> lookup PeanoNat.Nat.eq_dec (swap rel) x = Some x) ->
    equivalent_pairs_with_relation rel l l eq.
Proof.
  induction l; steps.
Qed.

Lemma has_polarities_rename_one:
  forall T X Y pol pols k,
    has_polarities (topen k T (fvar X type_var)) ((X, pol) :: pols) ->
    ~(X ∈ pfv T type_var) ->
    ~(Y ∈ pfv T type_var) ->
    ~(X ∈ support pols) ->
    ~(Y ∈ support pols) ->
    has_polarities (topen k T (fvar Y type_var)) ((Y, pol) :: pols).
Proof.
  intros.
  eapply (has_polarities_rename _ _ _ _ ((X,Y) :: idrel (pfv T type_var ++ support pols))); eauto 1;
    repeat step || apply equal_with_relation_topen || apply equal_with_idrel ||
           apply equivalent_with_pairs_cons || apply equivalent_pairs_with_relation ||
           apply equivalent_with_pairs_refl || rewrite swap_idrel in * ||
           apply idrel_lookup || apply equal_with_relation_refl2 ||
           rewrite range_idrel in * || list_utils.
Qed.

Lemma has_polarities_swap_aux:
  forall n T pols i j,
    type_nodes T < n ->
    has_polarities T pols ->
    has_polarities (swap_type_holes T i j) pols.
Proof.
  induction n; destruct T; repeat step || constructor || apply_any || step_inversion has_polarities;
    eauto with lia.

  exists X; repeat step || rewrite pfv_swap_type_holes in *.
  rewrite topen_swap2; steps.
  apply IHn; repeat step || autorewrite with bsize in *; try lia.
Qed.

Lemma has_polarities_swap:
  forall T pols i j,
    has_polarities T pols ->
    has_polarities (swap_type_holes T i j) pols.
Proof.
  eauto using has_polarities_swap_aux.
Qed.

Lemma has_polarities_topen_aux:
  forall n T pols X k,
    type_nodes T < n ->
    has_polarities T pols ->
    ~(X ∈ support pols) ->
    has_polarities (topen k T (fvar X type_var)) pols.
Proof.
  induction n; destruct T;
    repeat step || constructor || t_lookup ||
           step_inversion has_polarities || apply_any ||
           rewrite support_invert_polarities in *;
    eauto with lia;
    eauto using pair_in_list.

  define M (makeFresh ((X :: nil) :: pfv T3 type_var :: pfv (topen (S k) T3 (fvar X type_var)) type_var :: support pols :: nil)).
  exists M; steps; try finisher.

  rewrite open_swap; steps.
  apply_any; repeat step || autorewrite with bsize; eauto with lia; try finisher.

  rewrite topen_swap; repeat step || apply has_polarities_swap.
  apply has_polarities_rename_one with X0; steps; try finisher.
Qed.

Lemma has_polarities_topen:
  forall T pols X k,
    has_polarities T pols ->
    ~(X ∈ support pols) ->
    has_polarities (topen k T (fvar X type_var)) pols.
Proof.
  eauto using has_polarities_topen_aux.
Qed.
