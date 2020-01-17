Require Export SystemFR.StarInversions.
Require Export SystemFR.WFLemmasEval.
Require Export SystemFR.Equivalence.
Require Export SystemFR.LiftEquivalenceLemmas.

Require Import Coq.Strings.String.

Definition tlt (a: tree) (b: tree) :=
  app
    (notype_rec a
      (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
      (notype_lambda (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
    b.

Lemma tlt_def:
  forall a b,
    app
      (notype_rec a
        (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
        (notype_lambda (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
      b = tlt a b.
Proof.
  reflexivity.
Qed.

Ltac t_invert_app :=
  match goal with
  | H2: star scbv_step (app ?t1 ?t2) ?v |- _ =>
    poseNew (Mark H2 "inv app");
    unshelve epose proof (star_smallstep_app_inv _ v H2 _ t1 t2 eq_refl)
  end.

Lemma tlt_a_zero:
  forall a,
    star scbv_step (tlt a zero) ttrue ->
    False.
Proof.
  unfold tlt in *;
    repeat step || t_invert_star || star_smallstep_app_onestep || step_inversion cbv_value.
Qed.

Lemma star_pp:
  forall t t',
    star scbv_step t t' ->
    forall t1 t2, t = pp t1 t2 ->
      exists t1' t2', t'= pp t1' t2'.
Proof.
  induction 1; repeat step || t_invert_step; eauto.
Qed.

Lemma star_pp_succ:
  forall t1 t2 t,
    star scbv_step (pp t1 t2) (succ t) ->
    False.
Proof.
  intros.
  pose proof (star_pp _ _ H); steps.
Qed.

Lemma tlt_zero_b:
  forall b,
    cbv_value b ->
    star scbv_step (tlt zero b) ttrue ->
    1 <= tree_size b.
Proof.
  destruct 1; repeat step;
    eauto with omega;
    try solve [ inversion H; unfold tlt in *;
      repeat step || t_invert_step || star_smallstep_app_onestep || t_invert_star
    ].
Qed.

Lemma open_is_nat_value_wf:
  forall v i j rep,
    is_nat_value v ->
    wf rep 0 ->
    wf (open i v rep) j.
Proof.
  induction 1; steps.
Qed.

Hint Resolve open_is_nat_value_wf: wf.

Ltac reverse_once :=
  t_invert_star; repeat step || star_smallstep_value || step_inversion cbv_value || star_smallstep_app_onestep.

Lemma tlt_something:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    star scbv_step (tlt a b) ttrue ->
    exists b', b = succ b' /\
      (a = zero \/ exists a', a = succ a').
Proof.
  unfold tlt; steps.
  reverse_once; reverse_once; reverse_once; eauto.
Qed.
(*
Notation "'λ' t" := (notype_lambda t) (at level 80).
Notation "'recmatch' t '|' 'zero' '=>' t0 '|' 'succ' '_' '=>' ts" := (notype_rec t t0 ts)
  (at level 100,
  format "'recmatch'  t '/'  '|'  'zero'  '=>'  t0  '/' '|'  'succ'  '_'  '=>'  ts").
Notation "'mmatch' t '|' 'zero' '=>' t0 '|' 'succ' '_' '=>' ts" := (tmatch t t0 ts)
  (at level 100,
  format "'mmatch'  t '/'  '|'  'zero'  '=>'  t0  '/' '|'  'succ'  '_'  '=>'  ts").
Notation "'true'" := (ttrue).
Notation "'false'" := (tfalse).
Notation "'l_' i" := (lvar i term_var) (at level 80, format "'l_' i").
Notation "t1 '→*' t2" := (star scbv_step t1 t2) (at level 80).
Notation "t1 '→' t2" := (scbv_step t1 t2) (at level 80).
*)
Lemma tlt_succ:
  forall a b,
    cbv_value a ->
    cbv_value b ->
    wf a 0 ->
    star scbv_step (tlt (succ a) (succ b)) ttrue ->
    star scbv_step (tlt a b) ttrue.
Proof.
  unfold tlt; steps.

  reverse_once; eauto with values.
  reverse_once; eauto with values.
  reverse_once; eauto with values.
  reverse_once; eauto with values.

  repeat rewrite (open_none a) in * by eauto with wf;
    eauto using star_trans with cbvlemmas.
Qed.

Lemma tlt_sound:
  forall a, cbv_value a ->
    wf a 0 ->
    forall b, cbv_value b ->
    star scbv_step (tlt a b) ttrue ->
    tree_size a < tree_size b.
Proof.
  induction 1; steps; eauto using tlt_zero_b; eauto with lia;
    try solve [ apply_anywhere tlt_something; steps; eauto with values ].

  destruct H1; steps;
    try solve [ apply_anywhere tlt_something; steps; eauto with values ];
    eauto using le_n_S, tlt_succ.
Qed.

Ltac t_tlt_sound :=
  match goal with
  | H: star scbv_step (tlt ?a ?b) ttrue |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ _ b _ H)
  | H: equivalent_terms (tlt ?a ?b) ttrue |- _ =>
    cbv_value a; cbv_value b;
    poseNew (Mark (a,b) "tlt_sound");
    unshelve epose proof (tlt_sound a _ _ b _ _)
  end.

Lemma open_tlt:
  forall a b k rep, open k (tlt a b) rep = tlt (open k a rep) (open k b rep).
Proof.
  unfold tlt; repeat step.
Qed.

Lemma pfv_tlt:
  forall a b tag, pfv (tlt a b) tag = pfv a tag ++ pfv b tag.
Proof.
  unfold tlt; repeat step || rewrite List.app_nil_r in *.
Qed.

Lemma psubstitute_tlt:
  forall a b l tag,
    psubstitute (tlt a b) l tag = tlt (psubstitute a l tag) (psubstitute b l tag).
Proof.
  unfold tlt; repeat step.
Qed.

Ltac one_step_aux :=
 eapply Trans; [ eauto using is_nat_value_build_nat with values smallstep cbvlemmas | idtac ];
   repeat step || (rewrite open_none in * by (repeat step; eauto using is_nat_value_build_nat with wf)).

Ltac one_step := unshelve one_step_aux; steps.

Lemma tlt_complete:
  forall a b,
    a < b ->
    star scbv_step (tlt (build_nat a) (build_nat b)) ttrue.
Proof.
  unfold tlt; induction a; destruct b; repeat step || eauto with omega || one_step.
Qed.

Lemma is_nat_value_buildable:
  forall v, is_nat_value v ->
    exists n, v = build_nat n.
Proof.
  induction 1; steps.
  - exists 0; steps.
  - exists (S n); steps.
Qed.

Ltac t_is_nat_value_buildable :=
  match goal with
  | H: is_nat_value ?v |- _ =>
    poseNew (Mark v "is_nat_value_buildable");
    pose proof (is_nat_value_buildable v H)
  end.

Lemma tree_size_build_nat:
  forall n, tree_size (build_nat n) = n.
Proof.
  induction n; steps.
Qed.

Lemma tlt_complete2:
  forall a b,
    is_nat_value a ->
    is_nat_value b ->
    tree_size a < tree_size b ->
    star scbv_step (tlt a b) ttrue.
Proof.
  repeat step || t_is_nat_value_buildable || apply tlt_complete || rewrite tree_size_build_nat in *.
Qed.

Lemma true_is_irred: irred ttrue.
Proof.
  unfold irred; repeat step || t_nostep.
Qed.

Lemma equivalent_star_true:
  forall t1 t2,
    equivalent_terms t1 t2 ->
    star scbv_step t1 ttrue ->
    star scbv_step t2 ttrue.
Proof.
  unfold equivalent_terms, scbv_normalizing; steps.
  unshelve epose proof (H5 (ite (lvar 0 term_var) uu loop) _ _);
    steps.
  unshelve epose proof (H6 (ex_intro _ uu _)); repeat step || t_invert_star;
    eauto using star_trans with smallstep cbvlemmas;
    eauto using not_star_scbv_step_loop with exfalso.
Qed.

Lemma equivalent_true:
  forall t,
    equivalent_terms t ttrue ->
    star scbv_step t ttrue.
Proof.
  intros; eauto using equivalent_star_true, equivalent_sym with star.
Qed.

Lemma false_true_not_equivalent:
  equivalent_terms tfalse ttrue ->
  False.
Proof.
  repeat step || apply_anywhere equivalent_true || t_invert_star.
Qed.

Lemma equivalent_tlt_steps:
  forall t1 t2 v1 v2,
    equivalent_terms (tlt t1 t2) ttrue ->
    star scbv_step t1 v1 ->
    star scbv_step t2 v2 ->
    is_nat_value v1 ->
    is_nat_value v2 ->
    equivalent_terms (tlt v1 v2) ttrue.
Proof.
  unfold tlt; intros.
  apply equivalent_star; steps; eauto with erased wf.
  apply equivalent_true in H; steps.
  apply (star_many_steps _ (app
           (notype_rec v1 (notype_lambda (tmatch (lvar 0 term_var) tfalse ttrue))
              (notype_lambda
                 (tmatch (lvar 0 term_var) tfalse (app (app (lvar 2 term_var) uu) (lvar 0 term_var)))))
           t2)) in H; eauto with cbvlemmas; repeat step || unfold irred || t_nostep.
  inversion H; repeat step || t_invert_step || t_nostep || step_inversion cbv_value.

  - eapply Trans; eauto with smallstep; steps.
    eapply star_many_steps; eauto with cbvlemmas values; eauto using true_is_irred.
  - eapply Trans; eauto with smallstep; steps.
    eapply star_many_steps; eauto with cbvlemmas values; eauto using true_is_irred.
Qed.

Lemma is_erased_term_tlt:
  forall t1 t2,
    is_erased_term t1 ->
    is_erased_term t2 ->
    is_erased_term (tlt t1 t2).
Proof.
  unfold tlt; steps.
Qed.

Lemma wf_tlt:
  forall t1 t2 k,
    wf t1 k ->
    wf t2 k ->
    wf (tlt t1 t2) k.
Proof.
  unfold tlt; steps; eauto with lia.
Qed.

Lemma star_smallstep_tlt_left:
  forall t1 t2 t,
    star scbv_step t1 t2 ->
    star scbv_step (tlt t1 t) (tlt t2 t).
Proof.
  unfold tlt; steps; eauto with cbvlemmas.
Qed.

Opaque tlt.
Opaque loop.

Fixpoint nat_recognizer (v: tree): tree :=
  match v with
  | zero => tmatch (lvar 0 term_var) uu loop
  | succ v' => tmatch (lvar 0 term_var) loop (nat_recognizer v')
  | _ => uu
  end.

Lemma is_erased_term_nat_recognizer:
  forall v, is_erased_term (nat_recognizer v).
Proof.
  induction v;
    repeat step.
Qed.

Lemma wf_nat_recognizer:
  forall v, wf (nat_recognizer v) 1.
Proof.
  induction v;
    repeat step; eauto with wf; eauto using wf_loop.
Qed.

Lemma eval_nat_recognizer:
  forall v,
    is_nat_value v ->
    star scbv_step (open 0 (nat_recognizer v) v) uu.
Proof.
  induction 1;
    repeat step; eauto using star_one with smallstep.

  eapply Trans; eauto with smallstep values.
  rewrite (open_none _ 1); eauto using wf_nat_recognizer.
Qed.

Lemma normalizing_nat_recognizer:
  forall v,
    is_nat_value v ->
    forall v',
      cbv_value v' ->
      scbv_normalizing (open 0 (nat_recognizer v) v') ->
      v = v'
.
Proof.
  induction 1;
    repeat step; eauto using star_one with smallstep.

  - unfold scbv_normalizing in *; repeat step || t_invert_star || rewrite open_loop in *;
      eauto using not_star_scbv_step_loop with exfalso.

  - unfold scbv_normalizing in *;
      repeat step || t_invert_star || rewrite open_loop in *;
      eauto using not_star_scbv_step_loop with exfalso.

    clearMarked.
    rewrite (open_none _ 1) in H7 by eauto using wf_nat_recognizer.
    unshelve epose proof (IHis_nat_value v'0 _ _); steps; eauto.
Qed.

Lemma equivalent_value_nat:
  forall v v',
    cbv_value v ->
    is_nat_value v' ->
    equivalent_terms v v' ->
    v = v'.
Proof.
  unfold equivalent_terms; steps.
  unshelve epose proof (H6 (nat_recognizer v') _ _); steps;
    eauto using is_erased_term_nat_recognizer, wf_nat_recognizer.

  unshelve epose proof (H8 _);
    unfold scbv_normalizing; eauto using eval_nat_recognizer with values;
    eauto using eq_sym, normalizing_nat_recognizer.
Qed.

Lemma equivalent_nat:
  forall t v,
    is_nat_value v ->
    equivalent_terms t v ->
    star scbv_step t v.
Proof.
  intros.
  pose proof H0 as HH.
  unfold equivalent_terms in H0; steps.
  unshelve epose proof (H5 (lvar 0 term_var) _ _); steps.
  unshelve epose proof (H7 _); unfold scbv_normalizing; steps; eauto with star values.
  unfold scbv_normalizing in *; steps.
  unshelve epose proof (equivalent_value_nat v1 v _ _ _);
    repeat step;
    eauto using equivalent_star, equivalent_trans, equivalent_sym.
Qed.

Lemma equivalent_star_nat:
  forall t t' v,
    is_nat_value v ->
    equivalent_terms t t' ->
    star scbv_step t v ->
    star scbv_step t' v.
Proof.
  intros.
  pose proof H0 as HH; unfold equivalent_terms in HH; steps;
    eauto using equivalent_nat, equivalent_star, equivalent_trans, equivalent_sym.
Qed.
