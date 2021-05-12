Require Import SystemFR.Trees.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Syntax.
Require Import SystemFR.Evaluator.
Require Import SystemFR.FVLemmas.
Require Import SystemFR.FVLemmasClose.
Require Import SystemFR.ListUtils.
Require Import SystemFR.BigStep.
Require Import SystemFR.TOpenTClose.
Require Import SystemFR.RewriteTactics.
Require Import SystemFR.CloseLemmas.
Require Import SystemFR.WFLemmasClose.
Require Import SystemFR.WFLemmas.

Require Import Program.
Require Import Equations.Equations.
(* Require Import Equations.Prop.Subterm. *)

Require Import PeanoNat.
Require Import Relations.Relation_Operators.
Require Import Lia.

Section CPS.
Lemma open_t_size: forall t i nf, tree_size (open i t (fvar nf term_var)) = tree_size t.
Proof.
  induction t; steps.
Qed.

Equations (noind) cps_rec (t : tree) (next_fv : nat) : option tree by wf (tree_size t) lt := {
  cps_rec (fvar i f) _ := 
    match f with 
    | term_var => Some (notype_lambda (app (lvar 0 term_var) (fvar i term_var)))
    | type_var => None
    end;
  cps_rec uu _ := Some (notype_lambda (app (lvar 0 term_var) uu));
  cps_rec ttrue _ := Some (notype_lambda (app (lvar 0 term_var) ttrue));
  cps_rec tfalse _ := Some (notype_lambda (app (lvar 0 term_var) tfalse));
  cps_rec zero _ := Some (notype_lambda (app (lvar 0 term_var) zero));

  cps_rec (succ t') nf := None;
    (* if (is_value t') then 
      Some (notype_lambda (app (lvar 0 term_var) (succ (t')))) 
    else  *)
    (* option_map 
        (fun cps_t' => 
          (notype_lambda (
            app (lvar 0 term_var) (app cps_t' (notype_lambda (
              (succ (lvar 0 term_var)))
            ))
          ))
        )
        (cps_rec t' nf); *)
      (* option_map 
        (fun cps_t' => 
          (notype_lambda (
            app (cps_t') (notype_lambda (
              app (lvar 1 term_var) (succ (lvar 0 term_var))
            ))
          ))
        )
        (cps_rec t' nf); *)

  cps_rec (app t1 t2) nf :=  
    match (cps_rec t1 nf), (cps_rec t2 nf) with 
    | Some cps_t1, Some cps_t2 => 
      Some (notype_lambda (
        app (cps_t1) (notype_lambda (
          app (cps_t2) (notype_lambda (
            (* need to check the indexes here between 0 and 2 *)
            app (app (lvar 1 term_var) (lvar 0 term_var)) (lvar 2 term_var)
          ))
        ))
      ))
    | _, _ => None
    end;
  cps_rec (notype_lambda t) nf :=
    match (cps_rec (open 0 t (fvar nf term_var)) (S nf)) with 
    | Some csp_open_t => 
      Some (notype_lambda (
        app (lvar 0 term_var) (notype_lambda (
          (* Don't need to add the second lambda as it is included in csp_open_t *)
          close 0 csp_open_t nf
        ))
      ))
    | _ => None
    end;
    (* option_map
      (fun csp_open_t => 
        (notype_lambda (
          app (lvar 0 term_var) (notype_lambda (
            (* Don't need to add the second lambda as it is included in csp_open_t *)
            close 1 csp_open_t nf
          ))
        ))
      )
      (cps_rec (open 0 t (fvar nf term_var)) (S nf)); *)

  cps_rec (notype_tfix t) nf := None;

  cps_rec notype_err nf := None;
  cps_rec (ite cond tthen telse) nf := None;

  cps_rec (pp t1 t2) nf := None;
  cps_rec (pi1 t) nf := None;
  cps_rec (pi2 t) nf := None;
  
  cps_rec (tmatch t1 t0 ts) nf := None;
  cps_rec (sum_match t tl tr) nf := None;
  cps_rec (tleft t) nf := None;
  cps_rec (tright t) nf := None;
  cps_rec (boolean_recognizer r t) nf := None;
  cps_rec (unary_primitive o t) nf := None;
  cps_rec (binary_primitive o t1 t2) nf := None;
  cps_rec (tsize t) nf := None; (* I don't know how to handle it *) 
  
  cps_rec _ _ := None
}.

Ltac cps_rec_def := 
  try (rewrite open_t_size); lia.

Next Obligation.
 rewrite open_t_size; lia.
Qed. 
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Fail Next Obligation.

Definition cps (t : tree) := cps_rec t 0.

Definition cps_value (t : tree) : option tree := 
  match t with 
  | uu => Some uu
  | ttrue => Some ttrue
  | tfalse => Some tfalse 
  (* | pp e1 e2 => Some (pp e1 e2)
  | tleft e => Some (tleft e)
  | tright e => Some (tright e) *)
  | zero => Some zero 
  (* | succ e => Some uu *)
    (* option_map 
      (fun cps_e => app cps_e (notype_lambda (succ (lvar 0 term_var)))) 
      (cps_rec e 0) *) (*need to convert e *)
  | notype_lambda t' => 
    let open_t : tree := open 0 t' (fvar 0 term_var) in
    let cps_t : option tree := cps_rec open_t 1 in
    let close_t : option tree := option_map (fun cps_t => close 0 cps_t 0) cps_t in
      option_map (fun close_t => notype_lambda (close_t)) close_t
  | _ => None
  end.

Hint Unfold cps_value : cps.

Eval compute in cps (notype_lambda (lvar 0 term_var)).

Eval compute in cps_value (notype_lambda (lvar 0 term_var)).

Eval compute in (
  match (cps (notype_lambda (lvar 0 term_var))) with 
  | Some cps_t => eval (app cps_t (notype_lambda (lvar 0 term_var))) 1000
  | None => None 
  end
).

(* Eval compute in cps (app (notype_lambda (lvar 0 term_var)) uu).
Eval compute in (
  match (cps (app (notype_lambda (lvar 0 term_var)) uu)) with 
  | None => None
  | Some cps_t => (eval (app (cps_t) (notype_lambda (lvar 0 term_var))) 1000)
  end).

Eval compute in (
  option_map 
    (fun cps_t => eval (app cps_t (notype_lambda (lvar 0 term_var))) 1000)
    (cps (app (notype_lambda (lvar 0 term_var)) uu))
).

Eval compute in (
  let p : tree := app (app 
    (notype_lambda (notype_lambda (app (lvar 1 term_var) (lvar 0 term_var))))
    (notype_lambda (lvar 0 term_var))) uu
  in 
    option_map 
      (fun cps_t => eval (app cps_t (notype_lambda (lvar 0 term_var))) 1000)
      (cps p)
).

Eval compute in (
  let p : tree := (app 
    (notype_lambda (notype_lambda (app (lvar 1 term_var) (lvar 0 term_var))))
    (notype_lambda (lvar 0 term_var)))
  in 
    option_map 
      (fun cps_t => eval (app cps_t (notype_lambda (lvar 0 term_var))) 1000)
      (cps p)
).

Eval compute in (
  let t : tree := notype_lambda (lvar 0 term_var) in
  (cps t, cps_value t)
). *)

Opaque cps_rec.

Lemma cps_of_value_lambda: forall t cps_t cps_value_t, 
  cps (notype_lambda t) = Some cps_t ->
    cps_value (notype_lambda t) = Some cps_value_t ->
      notype_lambda (app (lvar 0 term_var) cps_value_t) = cps_t.
Proof.
  light.
  simpl in H0.
  unfold cps in H.
  simp cps_rec in H.
  destruct (cps_rec (open 0 t (fvar 0 term_var)) 1) eqn:E; inversion H0.
  inversion H.
  reflexivity.
Qed.

Eval compute in (
  eval (app (notype_lambda (app (lvar 0 term_var) uu))
  (notype_lambda (app (zero) (succ (lvar 0 term_var))))) 10
).

Lemma cps_of_value: forall v cps_v, 
  closed_value v -> cps v = Some cps_v -> exists cps_value_v, 
    cps_value v = Some cps_value_v /\ 
    (notype_lambda (app (lvar 0 term_var) cps_value_v)) = cps_v.
Proof.
  intros v cps_v [Hvclosed Hvvalue]. generalize dependent cps_v.
  induction Hvvalue; light; unfold cps in *; simp cps_rec in H; 
  repeat invert_constructor_equalities || step || options; eauto.
Qed.

Lemma cps_of_value': forall v cps_value_v, 
  closed_value v -> cps_value v = Some cps_value_v -> 
    cps v = Some (notype_lambda (app (lvar 0 term_var) cps_value_v)).
Proof.
Admitted.
  (* intros v cps_v [Hvclosed Hvvalue]. generalize dependent cps_v.
  induction Hvvalue; light; unfold cps in *; simp cps_rec in H; 
  repeat invert_constructor_equalities || step || options; eauto.
Qed. *)

Lemma cps_outputs_lambdas: forall p cps_p,
  cps p = Some cps_p -> exists b, cps_p = notype_lambda b.
Proof.
  induction p; unfold cps in *; simp cps_rec in *;
  repeat light || destruct_match || invert_constructor_equalities; eauto.
Qed.

Lemma cps_rec_nf: forall t nf nf', 
  (forall n, List.In n (pfv t term_var) -> n < nf) -> 
  (forall n, List.In n (pfv t term_var) -> n < nf') -> 
    cps_rec t nf = cps_rec t nf'.
Proof.
  
Admitted.


(* Lemma cps_of_value_is_value_for_lambda: forall t t', 
  closed_term (notype_lambda t) -> cps_value (notype_lambda t) = Some (notype_lambda).
Proof.
  
Qed.
*)

Lemma cps_of_value_is_value: forall v cps_v,
  closed_value v -> cps_value v = Some cps_v -> closed_value cps_v.
Proof.
  (* intros v cps_v [Hvclosed Hvvalue] H.
  induction Hvvalue; simpl in H; split;
  try solve [inversion H; repeat assumption || constructor];
  destruct (cps_rec (open 0 t (fvar 0 term_var)) 1) eqn:E; inversion H;
  try solve [constructor].
  repeat split; simpl. *)
Admitted. 

Lemma open_keeps_wf: forall t i n nf, wf t n -> wf (open i t (fvar nf term_var)) n.
Proof.
  induction t; light; steps.
Qed.

Lemma open_keeps_is_erased: forall t i n, 
  is_erased_term t -> is_erased_term (open i t (fvar n term_var)).
Proof.
  induction t; light; steps. 
Qed.

(* Lemma open_adds_to_fvs: forall t i fvs n,
  pfv t term_var = fvs -> pfv (open i t (fvar n term_var)) term_var = n :: fvs.
Proof.
  
Qed. *)

Lemma close_keeps_wf: forall t nf i n, 
  wf t n -> i < n -> wf (close i t nf) n.
Proof.
  induction t; light; steps;
  auto with lia.
Qed.

Lemma close_keeps_is_erased: forall t n i,
  is_erased_term t -> is_erased_term (close i t n).
Proof.
  induction t; light; steps.
Qed.

Lemma wf_S: forall t n,
  wf t n -> wf t (S n).
Proof.
  induction t; light; steps.
Qed.

Lemma le_add_l: forall n m o, n + m <= o -> n <= o.
Proof.
  lia.
Qed.

Lemma le_add_r: forall n m o, n + m <= o -> m <= o.
Proof.
  lia.
Qed.

Lemma cps_rec_outputs_erased_terms: forall size_t t nf cps_t,
  tree_size t <= size_t -> cps_rec t nf = Some cps_t -> is_erased_term cps_t.
Proof.
  induction size_t; light; destruct t; step; simp cps_rec in H0;
  repeat destruct_match; inversion H0; simpl; step; try lia; apply le_S_n in H.
  rewrite <- (open_t_size _ 0 nf) in H.
  apply (IHsize_t _ (S nf) t0) in H; try assumption.
  apply close_keeps_is_erased.
  assumption.
  remember H as H'.
  clear HeqH'.
  apply le_add_l in H.
  eapply IHsize_t; eassumption.
  apply le_add_r in H.
  eapply IHsize_t; eassumption.
Qed.

Ltac find_contradiction :=
  match goal with
  | H: forall n0, ?n = n0 \/ _ -> _ |- _ => unshelve epose proof H n _; clear H
  end.

Ltac apply_IH IH :=
  match goal with 
  | H: cps_rec (open 0 ?t (fvar ?nf term_var)) (S ?nf) = Some ?t',
    H': List.In ?x (pfv (close _ ?t' _) term_var) |- _ => 
    unshelve epose proof IH t _ nf t' x _ eq_refl _ H _; clear H
  end.

Lemma pfv_close: forall x nf t tag i, 
  x <> nf -> List.In x (pfv t tag) -> List.In x (pfv (close i t nf) tag).
Proof.
  induction t; repeat light || destruct_match || list_utils. 
Qed.

Ltac apply_IH_wf IH :=
  match goal with 
  | H: cps_rec ?t ?nf = Some ?t' |- _ => 
    unshelve epose proof IH t _ t' _ _ H; clear H
  end.

Lemma cps_rec_wf: forall size_t t nf cps_t,
  tree_size t < size_t -> 
    wf t nf -> cps_rec t nf = Some cps_t ->
      wf cps_t nf.
Proof.
  induction size_t; repeat light; try lia.
  destruct t; simp cps_rec in *; repeat light || destruct_match || 
    invert_constructor_equalities || apply_IH_wf IHsize_t || rewrite open_t_size;
  try lia;
  eauto with wf step_tactic;
  eauto using open_keeps_wf, close_keeps_wf with wf lia.
Qed.

Ltac apply_IH_pfv IH :=
  match goal with 
  | H: cps_rec ?t ?nf = Some ?t',
    H': List.In ?x (pfv ?t' term_var) |- _ => 
    unshelve epose proof IH t _ nf t' x _ eq_refl _ H _; clear H
  end.

Lemma cps_rec_pfv: forall size_t t fvs nf t' x,
  tree_size t < size_t -> pfv t term_var = fvs -> (forall n, List.In n fvs -> n < nf) ->
    cps_rec t nf = Some t' ->
      List.In x (pfv t' term_var) -> List.In x fvs.
Proof.
  induction size_t; light; try lia.
  destruct t eqn:E; try solve [inversion H; inversion H2;
  repeat destruct_match || invert_constructor_equalities || light || 
    simp cps_rec in * || contradiction || inversion H2 || find_contradiction; try lia].
  - (* lambda *)
    simpl in *.
    simp cps_rec in *.
    destruct_match; repeat light || invert_constructor_equalities
       || apply_IH_pfv IHsize_t || rewrite open_t_size || fv_close || fv_open || list_utils || destruct_match;
    try lia.
  - simpl in *.
    simp cps_rec in *.
    destruct_match; repeat light. destruct_match; repeat light.
    repeat light || list_utils || invert_constructor_equalities || apply_IH_pfv IHsize_t; 
    try lia;
    try solve [apply_any; list_utils; light];
    fv_close; apply pfv_close; light.
Qed.

Lemma cps_rec_pfv_nill: forall t nf cps_t,
    pfv t term_var = nil -> cps_rec t nf = Some cps_t -> pfv cps_t term_var = nil.
Proof.
  light.
  destruct (pfv cps_t term_var) eqn:E; auto.
  unshelve epose proof cps_rec_pfv (S (tree_size t)) t nil nf cps_t n _ _ _ _ _; 
  repeat light; try lia.
  rewrite E.
  repeat light.
Qed.

Lemma cps_value_pfv_nill: forall t cps_t,
    pfv t term_var = nil -> cps_value t = Some cps_t -> pfv cps_t term_var = nil.
Proof.
  light.
  destruct t; 
  repeat light || invert_constructor_equalities || options || destruct_match.
  unshelve epose proof cps_rec_pfv 
    (S (tree_size t)) (open 0 t (fvar 0 term_var)) (0::nil) 1 t1 0 _ _ _ _; 
  auto; repeat light; try lia.
  rewrite open_t_size; lia.
Admitted.

Lemma cps_keeps_closed_terms_closed: forall t cps_t, 
  closed_term t -> cps t = Some cps_t -> closed_term cps_t.
Proof.
  unfold closed_term. repeat light;
  eauto using cps_rec_wf, cps_rec_outputs_erased_terms, cps_rec_pfv_nill.
Qed.

(* Lemma cps_rec_correct: 
  forall p v, p ~~>* v -> wf p 0 -> is_erased_term p -> 
    forall cps_p nf,
      cps_rec p nf = Some cps_p -> 
        exists cps_v, cps_value v = Some cps_v /\
        (app cps_p (notype_lambda (lvar 0 term_var))) ~~>* cps_v.
Proof.
  induction 1; light; simp cps_rec in *; 
  try solve [ repeat invert_constructor_equalities || destruct_match || light || options || simpl;
  eexists; light; repeat econstructor].
  destruct_match; light. invert_constructor_equalities. options.
  destruct_match; light. 
  destruct_match; light.
  invert_constructor_equalities.
  eexists; light.
Admitted. *)

Lemma open_closed_term: forall b v, 
  closed_term (notype_lambda b) -> 
  closed_term v -> 
    closed_term (open 0 b v).
Proof.
  induction b; light; t_closing. lia.
Qed.

Lemma cps_rec_subst: forall v cps_v x, 
  closed_value v -> cps_value v = Some cps_v -> forall p_size p nf,
  tree_size p < p_size -> x < nf ->
  (forall n, List.In n (pfv p term_var) -> n < nf) ->
    cps_rec (substitute p ((x, v)::nil)) nf = 
    option_map (fun cps_p => substitute cps_p ((x, cps_v)::nil)) (cps_rec p nf).
Proof.
  induction p_size; try lia; light; destruct p;
  try solve [
    repeat light || simp cps_rec in * || destruct_match
      || invert_constructor_equalities || t_equality].
  - repeat light || simp cps_rec in * || destruct_match
      || invert_constructor_equalities || t_equality.
    rewrite (cps_rec_nf _ _ 0); try t_closer.
    eauto using cps_of_value'.
  - repeat light || simp cps_rec in *
    || invert_constructor_equalities || t_equality.
    unshelve epose proof IHp_size (open 0 p (fvar nf term_var)) (S nf) _ _ _;
    repeat light || fv_open || list_utils || rewrite open_t_size ||
      invert_constructor_equalities;
    try lia.
    try solve [repeat destruct_match || light].
    rewrite substitute_open2 in *; repeat light || t_closer 
      || invert_constructor_equalities || t_equality; try lia;
    try solve [repeat destruct_match || light; lia].
    repeat light || destruct_match || invert_constructor_equalities || t_equality.
    rewrite substitute_close; repeat light; try lia.
    eapply cps_value_pfv_nill; eauto.
    t_closer.
  - repeat light || simp cps_rec in *
    || invert_constructor_equalities || t_equality || list_utils.
    unshelve epose proof IHp_size p1 nf _ _ _; 
    unshelve epose proof IHp_size p2 nf _ _ _;
    repeat light || list_utils || rewrite open_t_size ||
      invert_constructor_equalities;
    try lia;
    try solve [apply_any; repeat light || list_utils].
    repeat light || destruct_match || invert_constructor_equalities.
Qed.

Lemma cps_subst: forall v cps_v x nf, 
  closed_value v -> cps_value v = Some cps_v -> forall p, x < nf ->
  (forall n, List.In n (pfv p term_var) -> n < nf) ->
    cps_rec (substitute p ((x, v)::nil)) nf = 
    option_map (fun cps_p => substitute cps_p ((x, cps_v)::nil)) (cps_rec p nf).
Proof.
  eauto using cps_rec_subst.
Qed.

Lemma cps_rec_defined_for_erased_wf_terms: forall t nf, 
  wf t 0 -> is_erased_term t -> exists cps_t, cps_rec t nf = Some cps_t.
Proof.
Admitted.

Lemma cps_defined_for_erased_wf_terms: forall t, 
  wf t 0 -> is_erased_term t -> exists cps_t, cps t = Some cps_t.
Proof.
Admitted.

Hint Resolve cps_defined_for_erased_wf_terms cps_rec_defined_for_erased_wf_terms: cps.

Theorem cps_eval: 
  forall p v, p ~~>* v -> closed_term p ->
    forall cps_p, cps p = Some cps_p -> 
      exists cps_v, cps_value v = Some cps_v /\ (
        forall k r, closed_value k -> 
          (app k (cps_v)) ~~>* r -> 
            (app cps_p k) ~~>* r
      ).
Proof.
  induction 1; light; unfold cps in *; simp cps_rec in *;
  try solve [repeat invert_constructor_equalities || destruct_match || light || options;
  eexists; repeat light; econstructor; t_closer; auto].
  - (* lambda *)
    repeat invert_constructor_equalities || destruct_match || light || options.
    eexists; repeat light.
    econstructor; repeat light; try solve [eapply value_bs; t_closer]. light.
    rewrite open_none; auto with bcbv_step.
    apply close_keeps_wf; try lia.
    eapply cps_rec_wf; eauto. apply wf_monotone2, wf_open; repeat light.
    t_closing.
  - (* app *)
    unshelve epose proof bs_closed_term t2 v2 _ _;
    unshelve epose proof bs_closed_term t1 (notype_lambda b1) _ _; t_closer.
    unshelve epose proof cps_rec_defined_for_erased_wf_terms (open 0 b1 (fvar 0 term_var)) 1 _ _.
    apply wf_open; t_closer.
    apply is_erased_open; t_closer.
    repeat invert_constructor_equalities || destruct_match || light || options || step.
    unshelve epose proof IHbcbv_step2 _ _ eq_refl; repeat step; try solve [
    unfold closed_value; light; eauto with values; eapply bs_closed_term; eauto;
      t_closer
    ]; t_closer.
    unshelve epose proof IHbcbv_step3 _ (substitute cps_t ((0, cps_v)::nil)) _; eauto.
    + t_closer.
    + unshelve epose proof cps_subst _ _ 0 1 _ H6 (open 0 b1 (fvar 0 term_var)) _ _; 
      repeat light; try lia.
      * unshelve epose proof bs_value t2 v2 _; t_closer.
      * repeat light || list_utils || fv_open; t_closer.
      * rewrite substitute_open3 in *; t_closer.
        t_substitutions.
        rewrite matched2 in *; repeat light.
        rewrite (cps_rec_nf _ _ 0) in H3; repeat light || fv_open; t_closer.
    + repeat step.
      eexists; light; eauto.
      econstructor; eauto with bcbv_step; repeat light;
      try solve [eapply value_bs; t_closer].
      rewrite open_none; [idtac | admit].
      rewrite open_none; [idtac | admit].
      unshelve epose proof IHbcbv_step1 _ _ eq_refl; repeat step;
      t_closer; try solve [
        unfold closed_value; light; eauto with values; eapply bs_closed_term; eauto;
      t_closer].
      apply_any. (* From IHbcbv_step1 *)
      * admit.  
      * econstructor; eauto with bcbv_step; repeat light;
        try solve [eapply value_bs; t_closer].
        rewrite open_none; [idtac | admit].
        rewrite open_none; [idtac | admit].
        apply_any. (* From IHbcbv_step2 *)
        -- admit.
        -- econstructor; eauto with bcbv_step; repeat light;
          try solve [eapply value_bs; t_closer].
          eapply value_bs. 
          apply cps_of_value_is_value with v2; eauto.
          t_closer.
          rewrite (open_none k); t_closer.
          rewrite open_none; [idtac | admit].
          apply ss_bs with (app (psubstitute cps_t ((0, cps_v) :: nil) term_var) k);
          auto. (* From IHbcbv_step3 *)
          constructor.
          rewrite <- open_close with (k := 0); [idtac | admit].
          constructor.
          admit.
Qed.

Theorem cps_correct: 
  forall p v, p ~~>* v -> closed_value v ->
    closed_term p -> forall cps_p, cps p = Some cps_p -> 
      exists cps_v, cps_value v = Some cps_v /\
        (app cps_p (notype_lambda (lvar 0 term_var))) ~~>* cps_v.
Proof.
  induction 1; light; unfold cps in *; simp cps_rec in *; 
  try solve [
  repeat invert_constructor_equalities || destruct_match || light || options;
  eexists; repeat simpl || light || econstructor].
  - (* lambda *)
    repeat invert_constructor_equalities || destruct_match || light || options.
    eexists; repeat light.
    econstructor; repeat light; eauto with bcbv_step. light.
    econstructor; repeat light; eauto with bcbv_step. light.
    rewrite open_none; auto with bcbv_step.
    unfold closed_term in *; repeat light.
    apply close_keeps_wf; try lia.
    apply wf_monotone2.
    eapply cps_rec_wf; eauto; eauto with wf step_tactic.
  - (* app *)
    repeat invert_constructor_equalities || destruct_match || light || options.
    + unshelve epose proof IHbcbv_step1 _ _ _ eq_refl; repeat step;
      t_closer;
      try solve [
      unfold closed_value; light; eauto with values; eapply bs_closed_term; eauto;
      t_closer].
      unshelve epose proof IHbcbv_step2 _ _ _ eq_refl; repeat step; try solve [
        unfold closed_value; light; eauto with values; eapply bs_closed_term; eauto;
        t_closer
      ]; t_closer.
      eexists. light.
      Focus 2.
      econstructor; eauto with bcbv_step; repeat light.
      rewrite open_none; try solve [
        t_closing; eauto using cps_rec_wf
      ].
      rewrite open_none; try solve [
        t_closing; eauto using cps_rec_wf, wf_monotone2
      ]. 
      econstructor; eauto with bcbv_step; repeat light.
      admit.

      (* unshelve epose proof H4 _ _ _; repeat step. *)

    admit.
    destruct_match; light; destruct_match; light; invert_constructor_equalities.
    repeat light.
    destruct_match; repeat light.
Admitted.

End CPS.
