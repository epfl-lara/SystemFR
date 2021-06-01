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

Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.

Require Import Program.
Require Import Equations.Equations.
Require Import Equations.Prop.Subterm.

Require Import PeanoNat.
Require Import Relations.Relation_Operators.
Require Import Lia.

Lemma open_t_size: forall t i nf, tree_size (open i t (fvar nf term_var)) = tree_size t.
Proof.
  induction t; steps.
Qed.

Hint Rewrite open_t_size : cps.

Equations cps_rec (value : bool) (t : tree) (next_fv : nat) : option tree by wf (tree_size t) lt := {
  cps_rec false (fvar i f) _ := 
    match f with 
    | term_var => Some (notype_lambda (app (lvar 0 term_var) (fvar i term_var)))
    | type_var => None
    end;
  cps_rec false uu _ := Some (notype_lambda (app (lvar 0 term_var) uu));
  cps_rec false ttrue _ := Some (notype_lambda (app (lvar 0 term_var) ttrue));
  cps_rec false tfalse _ := Some (notype_lambda (app (lvar 0 term_var) tfalse));
  cps_rec false zero _ := Some (notype_lambda (app (lvar 0 term_var) zero));
  cps_rec false (succ t') nf := 
    if (is_value t') then 
      option_map 
        (fun cps_v => notype_lambda (app (lvar 0 term_var) (succ (cps_v))))
        (cps_rec true t' nf)
    else 
      option_map 
        (fun cps_t' => 
          (notype_lambda (
            app (cps_t') (notype_lambda (
              app (lvar 1 term_var) (succ (lvar 0 term_var))
            ))
          ))
        )
        (cps_rec false t' nf);
  cps_rec false (app t1 t2) nf :=  
    match (cps_rec false t1 nf), (cps_rec false t2 nf) with 
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
  cps_rec false (notype_lambda t) nf :=
    match (cps_rec false (open 0 t (fvar nf term_var)) (S nf)) with 
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

  cps_rec false (notype_tfix t) nf := None;

  cps_rec false notype_err nf := None;
  cps_rec false (ite cond tthen telse) nf := None;

  cps_rec false (pp t1 t2) nf := None;
  cps_rec false (pi1 t) nf := None;
  cps_rec false (pi2 t) nf := None;
  
  cps_rec false (tmatch t1 t0 ts) nf := None;
  cps_rec false (sum_match t tl tr) nf := None;
  cps_rec false (tleft t) nf := None;
  cps_rec false (tright t) nf := None;
  cps_rec false (boolean_recognizer r t) nf := None;
  cps_rec false (unary_primitive o t) nf := None;
  cps_rec false (binary_primitive o t1 t2) nf := None;
  cps_rec false (tsize t) nf := None; (* I don't know how to handle it *) 
  
  cps_rec false _ _ := None;

  (* CPS value *)
  cps_rec true uu _ := Some uu;
  cps_rec true ttrue _ := Some ttrue;
  cps_rec true tfalse _ := Some tfalse;
  cps_rec true (pp e1 e2) _ := None;
  cps_rec true (tleft e) _ := None;
  cps_rec true (tright e) _ := None;
  cps_rec true zero _ := Some zero;
  cps_rec true (succ e) nf := 
    option_map succ (cps_rec true e nf);
  cps_rec true (notype_lambda t') nf :=
    let open_t : tree := open 0 t' (fvar nf term_var) in
    let cps_t : option tree := cps_rec false open_t (S nf) in
    let close_t : option tree := option_map (fun cps_t => close 0 cps_t nf) cps_t in
      option_map (fun close_t => notype_lambda (close_t)) close_t;
  cps_rec true _ nf := None
}.

Ltac cps_rec_def := try solve [rewrite open_t_size; lia]; lia.

(* Solve Obligations with cps_rec_def. *)
Next Obligation. cps_rec_def. Qed.
Next Obligation. cps_rec_def. Qed.
Next Obligation. cps_rec_def. Qed.
Next Obligation. cps_rec_def. Qed.
Fail Next Obligation.

Definition cps (t : tree) := cps_rec false t 0.

Definition cps_value (t : tree) := cps_rec true t 0.

(* Fixpoint cps_value (t : tree) : option tree := 
  match t with 
  | uu => Some uu
  | ttrue => Some ttrue
  | tfalse => Some tfalse 
  (* | pp e1 e2 => Some (pp e1 e2)
  | tleft e => Some (tleft e)
  | tright e => Some (tright e) *)
  | zero => Some zero 
  | succ e => 
    option_map 
      succ 
      (* (fun cps_e => app cps_e (notype_lambda (succ (lvar 0 term_var))))  *)
      (cps_value e) (* need to convert e *)
  | notype_lambda t' => 
    let open_t : tree := open 0 t' (fvar 0 term_var) in
    let cps_t : option tree := cps_rec open_t 1 in
    let close_t : option tree := option_map (fun cps_t => close 0 cps_t 0) cps_t in
      option_map (fun close_t => notype_lambda (close_t)) close_t
  | _ => None
  end.

Hint Unfold cps_value : cps. *)

(* Eval compute in cps (notype_lambda (lvar 0 term_var)).

Eval compute in cps_value (notype_lambda (lvar 0 term_var)).

Eval compute in (
  match (cps (notype_lambda (lvar 0 term_var))) with 
  | Some cps_t => eval (app cps_t (notype_lambda (lvar 0 term_var))) 1000
  | None => None 
  end
). *)

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

(* Definition tree_eq_dec : forall (x y : tree), {x = y} + {x <> y}.
Proof.
  repeat decide equality || apply fv_tag_dec.
Defined.
Definition tree_eq t1 t2 : bool := if (tree_eq_dec t1 t2) then true else false. *)

(* Definition tree_eq_dec : forall (x y : option tree), {x = y} + {x <> y}.
Proof.
  repeat decide equality || apply fv_tag_dec.
Defined.
Definition tree_eq t1 t2 : bool := if (tree_eq_dec t1 t2) then true else false. *)

(* Eval compute in (
  let t : tree := succ (app (notype_lambda (succ (lvar 0 term_var))) zero) in
  let v : tree := succ (succ zero) in
  let cps_t := cps t in
  let cps_value_v := cps_value v in
  let final_t := 
    match cps_t with 
    | None => None 
    | Some t' => eval (app t' (notype_lambda (lvar 0 term_var))) 1000 
    end in
  (cps_t, cps_value_v, final_t)
). *)

(* closed_value v -> cps_value v = Some cps_v -> forall p, x < nf ->
  (forall n, List.In n (pfv p term_var) -> n < nf) ->
    cps_rec (substitute p ((x, v)::nil)) nf = 
    option_map (fun cps_p => substitute cps_p ((x, cps_v)::nil)) (cps_rec p nf).
     *)

(* Transparent tag_eq_dec. *)

(* Eval compute in (
  let v : tree := succ (zero) in
  let p : tree := fvar 0 term_var in 
  let x := 0 in
  (cps_rec false (v) 0,
  option_map (fun cps_p => substitute cps_p ((x, v)::nil)) (cps_rec false p 1))
). *)

Opaque cps_rec.

Require Import Coq.Classes.RelationClasses.

(* see https://github.com/coq/coq/issues/3814 *)
Instance: subrelation eq Basics.impl.
Proof.
  steps.
Qed.

Instance: subrelation eq (Basics.flip Basics.impl).
Proof.
  steps.
Qed.

Ltac simp_cps_hyp :=
  match goal with
  | H: _ |- _ => rewrite_strat outermost hints cps_rec in H
  end.

Ltac simp_cps_top_level_hyp :=
  match goal with
  | H: _ |- _ => rewrite_strat hints cps_rec in H
  end.

Ltac simp_cps_goal := rewrite_strat outermost hints cps_rec.

Ltac simp_cps_top_level_goal := rewrite_strat hints cps_rec.

Ltac simp_cps := simp_cps_hyp || simp_cps_goal.

(* Lemma cps_of_value_lambda: forall t cps_t cps_value_t, 
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
Qed. *)

(* Eval compute in (
  eval (app (notype_lambda (app (lvar 0 term_var) uu))
  (notype_lambda (app (zero) (succ (lvar 0 term_var))))) 10
). *)

Lemma cps_not_def_cps_value_not_def: forall t nf,
  cps_rec false t nf = None -> cps_rec true t nf = None.
Proof.
  induction t; 
  repeat light || simp_cps || options || destruct_match || instantiate_any.
Qed.

Lemma cps_of_value: forall v cps_v nf, 
  cbv_value v -> cps_rec false v nf = Some cps_v -> exists cps_value_v, 
    cps_rec true v nf = Some cps_value_v /\ 
    (notype_lambda (app (lvar 0 term_var) cps_value_v)) = cps_v.
Proof.
  unfold cps, cps_value;
  intros; generalize dependent cps_v; induction H; 
  repeat light || simp_cps || options  
  || invert_constructor_equalities; eauto;
  try (apply is_value_correct in H; rewrite_any);
  repeat light || destruct_match || invert_constructor_equalities;
  eexists; repeat light.
Qed.

(* Lemma cps_of_value': forall v cps_value_v, 
  closed_value v -> cps_value v = Some cps_value_v -> 
    cps v = Some (notype_lambda (app (lvar 0 term_var) cps_value_v)).
Proof.
  unfold cps; t_closing; generalize dependent cps_value_v;
  induction H2; simp cps_rec in *;
  try solve[repeat light || options || destruct_match || t_equality
   || invert_constructor_equalities].
  repeat light || options.
  destruct (cps_value v) eqn:E; repeat light || invert_constructor_equalities.
  unshelve epose proof H3 _ eq_refl.
  apply_anywhere is_value_correct.
  destruct (is_value v) eqn:E'; repeat light.
  rewrite_any; auto.
Qed. *)

Lemma cps_of_value'': forall v cps_value_v nf, 
  cbv_value v -> cps_rec true v nf = Some cps_value_v -> 
    cps_rec false v nf = Some (notype_lambda (app (lvar 0 term_var) cps_value_v)).
Proof.
  intros; generalize dependent cps_value_v;
  induction H; simp cps_rec in *;
  try solve[repeat light || options || destruct_match || t_equality
   || invert_constructor_equalities].
  repeat light || options.
  destruct (cps_rec true v nf) eqn:E; repeat light || invert_constructor_equalities.
  unshelve epose proof IHcbv_value _ eq_refl.
  apply_anywhere is_value_correct.
  destruct (is_value v) eqn:E'; repeat light.
Qed.

(* Lemma cps_outputs_lambdas: forall p cps_p,
  cps p = Some cps_p -> exists b, cps_p = notype_lambda b.
Proof.
  induction p; unfold cps in *; simp cps_rec in *;
  repeat light || destruct_match || invert_constructor_equalities; eauto.
Qed. *)

Definition is_variable (t : tree) nf : Prop := 
  match t with
  | fvar i term_var => i < nf
  | _ => False
  end.

Lemma sub_wfs: forall sub nf, 
  (forall s, List.In s (range sub) -> is_variable s nf) -> 
    wfs sub 0.
Proof.
  induction sub;
  repeat light || destruct_match || unfold is_variable in *.
  - unshelve epose proof H t _; repeat light || destruct_match.
  - eapply_any; repeat light.
    unshelve epose proof H s _; repeat light. eauto.
Qed.

Hint Resolve sub_wfs: wf.

Ltac rewrite_IH_subst_nf IHsize_t nf :=
  match goal with 
  | H : cps_rec false (psubstitute ?t ?sub term_var) ?nf' = Some ?t' |- _ => 
    poseNew (Mark (sub, t) "subst"); rewrite (IHsize_t _ _ nf) in H
  end.

Lemma substitute_close2: forall t k nf nf' sub, nf < nf' ->
  (forall s, List.In s (range sub) -> is_variable s nf') ->
  (forall x, List.In x (support sub) -> x < nf) ->
  (forall n, List.In n (pfv t term_var) -> n < nf') ->
    close k (psubstitute t ((nf, fvar nf' term_var) :: sub) term_var) nf' =
    psubstitute (close k t nf) sub term_var.
Proof.
  induction t; 
  repeat light || destruct_match || invert_constructor_equalities
   || t_equality || t_lookup || unfold is_variable in *; try lia;
  try solve [apply_any; auto; repeat light; apply_any; repeat list_utils; auto].
  - instantiate_any.
    repeat light || destruct_match; try lia.
  - unshelve epose proof H2 n _; lia.
Qed.

Lemma open_keeps_wf: forall t i n nf, wf t n -> wf (open i t (fvar nf term_var)) n.
Proof.
  induction t; light; steps.
Qed.

(* Lemma open_keeps_is_erased: forall t i n, 
  is_erased_term t -> is_erased_term (open i t (fvar n term_var)).
Proof.
  induction t; light; steps. 
Qed. *)

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

(* Lemma close_keeps_is_erased: forall t n i,
  is_erased_term t -> is_erased_term (close i t n).
Proof.
  induction t; light; steps.
Qed. *)

(* Lemma wf_S: forall t n,
  wf t n -> wf t (S n).
Proof.
  induction t; light; steps.
Qed. *)

(* Lemma le_add_l: forall n m o, n + m <= o -> n <= o.
Proof.
  lia.
Qed.

Lemma le_add_r: forall n m o, n + m <= o -> m <= o.
Proof.
  lia.
Qed. *)

Lemma cps_rec_outputs_erased_terms': forall size_t t nf cps_t value,
  cps_rec value t nf = Some cps_t -> tree_size t < size_t -> is_erased_term cps_t.
Proof.
  induction size_t; try lia; destruct t; destruct value; 
  repeat light || simp_cps || destruct_match || 
    invert_constructor_equalities || options;
  eauto with lia.
  - rewrite <- (open_t_size _ 0 nf) in H0.
    apply (IHsize_t _ (S nf) t1) in matched0; try lia.
    auto with erased.
  - unshelve epose proof IHsize_t _ _ _ _ matched _.
    rewrite open_t_size; lia.
    auto with erased.
Qed.

Lemma cps_rec_outputs_erased_terms: forall t nf cps_t value,
  cps_rec value t nf = Some cps_t -> is_erased_term cps_t.
Proof.
  eauto using cps_rec_outputs_erased_terms'.
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
  | H: cps_rec _ ?t ?nf = Some ?t' |- _ => 
    unshelve epose proof IH t _ t' _ _ _ H; clear H
  end.

Lemma cps_rec_wf': forall size_t t nf cps_t value,
  tree_size t < size_t -> 
    wf t 0 -> cps_rec value t nf = Some cps_t ->
      wf cps_t 0.
Proof.
  induction size_t; repeat light; try lia;
  destruct t; destruct value; simp_cps; repeat light || destruct_match || 
    invert_constructor_equalities || apply_IH_wf IHsize_t || rewrite open_t_size 
    || options;
  try lia;
  eauto with wf step_tactic;
  eauto using open_keeps_wf, close_keeps_wf with wf lia.
Qed.

Lemma cps_rec_wf: forall t nf cps_t value,
  cps_rec value t nf = Some cps_t -> wf t 0 -> 
    wf cps_t 0.
Proof.
  eauto using cps_rec_wf'.
Qed.

Ltac apply_IH_pfv IH :=
  match goal with 
  | H: cps_rec _ ?t ?nf = Some ?t',
    H': List.In ?x (pfv ?t' term_var) |- _ => 
    unshelve epose proof IH t _ nf t' x _ H _ eq_refl _ _; clear H
  end.
(* To use carefully as it might loop in repeat *)
Ltac apply_IH_pfv_lite IH :=
  match goal with 
  | H: cps_rec _ ?t ?nf = Some _,
    H': List.In ?x (pfv ?t' term_var) |- _ => 
      poseNew (Mark (t, t') "IH applied");
      unshelve epose proof IH t _ nf _ x _ H _ eq_refl _ _; clear H
  end.

Ltac apply_in_list := 
  match goal with 
  | H: forall n, List.In n (?s1 ++ ?s2) -> _,
    H': List.In ?n ?s1 |- _ => 
      unshelve epose proof H n _; repeat light || list_utils
 | H: forall n, List.In n (?s1 ++ ?s2) -> _,
   H': List.In ?n ?s2 |- _ => 
      unshelve epose proof H n _; repeat light || list_utils
  end.

Lemma cps_rec_pfv': forall size_t t fvs nf t' x value,
  cps_rec value t nf = Some t' ->
    tree_size t < size_t -> pfv t term_var = fvs -> (forall n, List.In n fvs -> n < nf) ->
      List.In x (pfv t' term_var) -> List.In x fvs.
Proof.
  induction size_t; light; try lia.
  destruct t eqn:E; destruct value;
  repeat light || simp_cps_hyp || destruct_match
    || invert_constructor_equalities || list_utils || apply_IH_pfv IHsize_t
    || rewrite open_t_size || fv_close || fv_open || apply_in_list || options; try lia.
Qed.

Lemma cps_rec_pfv: forall t fvs nf t' x value,
  cps_rec value t nf = Some t' ->
    pfv t term_var = fvs -> (forall n, List.In n fvs -> n < nf) ->
      List.In x (pfv t' term_var) -> List.In x fvs.
Proof.
  eauto using cps_rec_pfv'.
Qed.

Lemma cps_rec_pfv_nill: forall t nf cps_t value,
  pfv t term_var = nil -> cps_rec value t nf = Some cps_t -> pfv cps_t term_var = nil.
Proof.
  light.
  destruct (pfv cps_t term_var) eqn:E; auto.
  unshelve epose proof cps_rec_pfv t nil nf cps_t n _ _ _ _ _; 
  repeat light; try lia.
  rewrite E.
  repeat light.
Qed.

(* Lemma cpr_rec_pfv': forall t fvs nf cps_t,
  pfv t term_var = fvs -> (forall n, List.In n fvs -> n < nf) ->
    cps_rec t nf = Some cps_t -> pfv cps_t term_var = fvs.
Proof.
  light.
  destruct fvs eqn:E; eauto using cps_rec_pfv_nill.
  destruct (pfv cps_t term_var) eqn:E'; auto.
  - unshelve epose proof cps_rec_pfv (S (tree_size t)) t nil nf cps_t n _ _ _ _ _;
    repeat light.
    rewrite H.
Admitted. *)

Lemma fv_close':
  forall t k x y ys,
    pfv (close k t x) term_var = y::ys ->
    y <> x /\ y ∈ pfv t term_var.
Proof.
  intros.
  eapply fv_close.
  rewrite H.
  steps.
Qed.

Lemma cps_value_of_value: forall v cps_v, 
  cbv_value v -> cps_value v = Some cps_v -> cbv_value cps_v.
Proof.
  unfold cps_value; light; generalize dependent cps_v; induction H;
  repeat simp_cps || options || destruct_match || invert_constructor_equalities || light;
  eauto with values.
Qed.

Lemma cps_value_wf: forall v cps_v,
  wf v 0 -> cps_value v = Some cps_v -> wf cps_v 0.
Proof.
  eauto using cps_rec_wf.
Qed.

Lemma cps_value_pfv_nill: forall t cps_t,
  pfv t term_var = nil -> cps_value t = Some cps_t -> pfv cps_t term_var = nil.
Proof.
  eauto using cps_rec_pfv_nill.
Qed.

Lemma cps_value_is_earased: forall v cps_v,
  is_erased_term v -> cps_value v = Some cps_v -> is_erased_term cps_v.
Proof.
  eauto using cps_rec_outputs_erased_terms.
Qed.

Lemma cps_of_closed_value_is_value: forall v cps_v,
  closed_value v -> cps_value v = Some cps_v -> closed_value cps_v.
Proof.
  t_closing; 
  eauto using cps_value_pfv_nill, cps_value_wf, cps_value_of_value, cps_value_is_earased.
Qed.

Lemma fv_close_nil2:
  forall t k x,
    subset (pfv t term_var) (x :: nil) ->
    pfv (close k t x) term_var = nil.
Proof.
  induction t; repeat step || list_utils || sets.
Qed.

Lemma fv_close_cps_rec: forall t cps_t k x nf value, 
  pfv t term_var = nil -> x < nf -> 
  cps_rec value (open k t (fvar x term_var)) nf = Some cps_t ->
    subset (pfv cps_t term_var) (x::nil).
Proof.
  unfold subset; repeat light.
  left.
  eapply cps_rec_pfv in H1; eauto; 
  repeat light || fv_open || list_utils || destruct_match.
Qed.

Lemma cps_keeps_closed_terms_closed: forall t cps_t, 
  closed_term t -> cps t = Some cps_t -> closed_term cps_t.
Proof.
  unfold closed_term. repeat light;
  eauto using cps_rec_wf, cps_rec_outputs_erased_terms, cps_rec_pfv_nill.
Qed.

Lemma substitute_value: forall t sub tag,
  cbv_value t -> cbv_value (psubstitute t sub tag).
Proof.
  induction 1; repeat light; eauto with values.
Qed.

Lemma substitute_is_value: forall t sub tag,
  is_value t = true -> is_value (psubstitute t sub tag) = true.
Proof.
  repeat light.
  apply is_value_correct in H. apply is_value_correct.
  eauto using substitute_value.
Qed.

Lemma substitute_vars_not_value: forall t sub tag nf nf', nf < nf' ->
  (forall n, List.In n (pfv t term_var) -> n < nf) -> 
  (forall s, List.In s (range sub) -> is_variable s nf') ->
  (forall x, List.In x (support sub) -> x < nf) ->
    cbv_value (psubstitute t sub tag) -> cbv_value t.
Proof.
  induction t; repeat light; eauto with values; inversion H3;
  repeat light || destruct_match || destruct_tag || 
  t_lookup || instantiate_any || constructor;
  eapply_any; eauto; repeat light; apply H0; repeat light || list_utils.
Qed.

Lemma substitute_vars_not_is_value': forall t sub tag nf nf', nf < nf'->
  (forall n, List.In n (pfv t term_var) -> n < nf) -> 
  (forall s, List.In s (range sub) -> is_variable s nf') ->
  (forall x, List.In x (support sub) -> x < nf) ->
    is_value (psubstitute t sub tag) = true -> is_value t = true.
Proof.
  repeat light;
  apply is_value_correct in H3. apply is_value_correct.
  eauto using substitute_vars_not_value.
Qed.

Lemma substitute_vars_not_is_value: forall t sub tag nf nf', 
  is_value t = false -> 
  nf < nf'->
  (forall n, List.In n (pfv t term_var) -> n < nf) -> 
  (forall s, List.In s (range sub) -> is_variable s nf') ->
  (forall x, List.In x (support sub) -> x < nf) ->
    is_value (psubstitute t sub tag) = false.
Proof.
  repeat light.
  destruct (is_value (psubstitute t sub tag)) eqn:E; auto.
  eapply substitute_vars_not_is_value' in E; eauto.
Qed.

Ltac apply_subst_is_value sub tag nf nf' :=
  match goal with 
  | H: is_value ?t = true |- _ => apply (substitute_is_value t sub tag) in H
  | H: is_value ?t = false |- _ => 
    apply (substitute_vars_not_is_value t sub tag nf nf') in H; eauto
  end.


Lemma cps_rec_subst_nf': forall size_t t sub nf nf', 
  tree_size t < size_t -> nf < nf' ->
  (forall n, List.In n (pfv t term_var) -> n < nf) -> 
  (forall s, List.In s (range sub) -> is_variable s nf') ->
  (forall x, List.In x (support sub) -> x < nf) ->
    cps_rec false (substitute t sub) nf' = 
    option_map (fun res => substitute res sub)
    (cps_rec false t nf).
Proof.
  induction size_t; try lia; destruct t;
  repeat light || simp_cps || invert_constructor_equalities 
  || t_equality || options || destruct_tag;
  try solve [repeat light || simp_cps || invert_constructor_equalities 
  || t_equality || destruct_match].
  - repeat light || simp_cps || invert_constructor_equalities 
    || t_equality || destruct_match.
    repeat t_lookup.
    instantiate_any.
    unfold is_variable in *;
    destruct_match; repeat light.
    repeat simp_cps || light || destruct_match.
  - unshelve epose proof IHsize_t (open 0 t (fvar nf term_var)) 
    ((nf, fvar nf' term_var)::sub) (S nf) (S nf') _ _ _ _ _;
    try solve [repeat light || rewrite open_t_size || options 
    || destruct_match || invert_constructor_equalities || fv_open || list_utils || t_pfv_in_subst; try lia].
    + repeat light.
      instantiate_any.
      unfold is_variable in *;
      repeat destruct_match || light.
    + rewrite substitute_open3 in *; t_rewrite;
      unfold is_variable in *;
      try solve [repeat instantiate_any; lia].
      repeat rewrite_any || light || invert_constructor_equalities || t_equality.
      apply substitute_close2; repeat light.
      unfold is_variable; instantiate_any; light.
      unshelve epose proof cps_rec_pfv 
        _ _ _ _ n _ matched1 eq_refl _ _; try lia;
      repeat light || fv_open || list_utils || destruct_match.
      instantiate_any.
      lia.
  - unshelve epose proof IHsize_t t1 sub nf nf' _ _ _ _ _; 
    unshelve epose proof IHsize_t t2 sub nf nf' _ _ _ _ _;
    repeat light || rewrite open_t_size || options 
    || invert_constructor_equalities || fv_open
    || list_utils || t_pfv_in_subst; try lia;
    try solve [apply H1; repeat list_utils || light];
    try solve [instantiate_any; light].
    destruct (cps_rec false t2 nf) eqn:E; 
    destruct (cps_rec false t1 nf) eqn:E';
    repeat light || rewrite_any.
  - unshelve epose proof IHsize_t t sub nf nf' _ _ _ _ _; 
    repeat light; try lia; try solve [instantiate_any; light].
    destruct (cps_rec false t nf) eqn:C; repeat light || rewrite_any;
    destruct (is_value t) eqn:E; 
    remember E as E'; clear HeqE';
    apply_subst_is_value sub term_var nf nf'; 
    rewrite_any; auto; 
    apply is_value_correct in E; apply is_value_correct in E';
    try unshelve epose proof cps_of_value _ _ _ E C;
    try unshelve epose proof cps_of_value _ _ _ E' H4;
    eauto with step_tactic.
    apply cps_not_def_cps_value_not_def in C; 
    apply cps_not_def_cps_value_not_def in H4.
    rewrite H4, C; auto.
Qed.

Lemma cps_rec_subst_nf: forall t sub nf nf', 
  nf < nf' ->
  (forall n, List.In n (pfv t term_var) -> n < nf) -> 
  (forall s, List.In s (range sub) -> is_variable s nf') ->
  (forall x, List.In x (support sub) -> x < nf) ->
    cps_rec false (substitute t sub) nf' = 
    option_map (fun res => substitute res sub)
    (cps_rec false t nf).
Proof.
  eauto using cps_rec_subst_nf'.
Qed.

Lemma cps_rec_nf: forall t nf nf', 
  (forall n, List.In n (pfv t term_var) -> n < nf) -> 
  (forall n, List.In n (pfv t term_var) -> n < nf') -> 
    cps_rec false t nf = cps_rec false t nf'.
Proof.
  light.
  destruct (Compare_dec.lt_eq_lt_dec nf nf') as [[E | E] | E]; auto.
  - (* nf < nf' *)
    unshelve epose proof cps_rec_subst_nf t nil nf nf' _ _ _ _; auto;
    repeat light || options || destruct_match || rewrite substitute_nothing3 in *.
  - (* nf > nf' *)
    unshelve epose proof cps_rec_subst_nf t nil nf' nf _ _ _ _; auto;
    repeat light || options || destruct_match || rewrite substitute_nothing3 in *.
Qed.

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
    cps_rec false (substitute p ((x, v)::nil)) nf = 
    option_map (fun cps_p => substitute cps_p ((x, cps_v)::nil)) (cps_rec false p nf).
Proof.
  induction p_size; try lia; light; destruct p;
  try solve [
    repeat light || simp_cps || destruct_match
      || invert_constructor_equalities || t_equality].
  - repeat light || simp_cps || destruct_match
      || invert_constructor_equalities || t_equality.
    rewrite (cps_rec_nf _ _ 0); t_closing.
    eauto using cps_of_value''.
  - repeat light || simp_cps
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
  - repeat light || simp_cps
    || invert_constructor_equalities || t_equality || list_utils.
    unshelve epose proof IHp_size p1 nf _ _ _; 
    unshelve epose proof IHp_size p2 nf _ _ _;
    repeat light || list_utils || rewrite open_t_size ||
      invert_constructor_equalities;
    try lia;
    try solve [apply_any; repeat light || list_utils].
    repeat light || destruct_match || invert_constructor_equalities.
  - unshelve epose proof IHp_size p nf _ _ _; 
    repeat light || simp_cps; try lia.
Admitted.

Lemma cps_subst: forall v cps_v x nf, 
  closed_value v -> cps_value v = Some cps_v -> forall p, x < nf ->
  (forall n, List.In n (pfv p term_var) -> n < nf) ->
    cps_rec false (substitute p ((x, v)::nil)) nf = 
    option_map (fun cps_p => substitute cps_p ((x, cps_v)::nil)) (cps_rec false p nf).
Proof.
  eauto using cps_rec_subst.
Qed.

Lemma cps_rec_defined_for_erased_wf_terms: forall t nf, 
  wf t 0 -> is_erased_term t -> exists cps_t, cps_rec false t nf = Some cps_t.
Proof.
Admitted.

Lemma cps_defined_for_erased_wf_terms: forall t, 
  wf t 0 -> is_erased_term t -> exists cps_t, cps t = Some cps_t.
Proof.
Admitted.

#[global]
Hint Resolve cps_defined_for_erased_wf_terms cps_rec_defined_for_erased_wf_terms: cps.

Ltac solve_wf_cps_rec :=
  try solve [try apply wf_monotone2; eapply cps_rec_wf; eauto; t_closer].

Ltac solve_pfv_nill_cps_rec :=
  try solve [eapply cps_rec_pfv_nill; eauto].

Ltac solve_erased_terms_cps_rec :=
  try solve [eapply cps_rec_outputs_erased_terms; eauto].

(* Ltac instantiate_IH_cps_eval IH := *)

Theorem cps_eval: 
  forall p v, p ~~>* v -> closed_term p ->
    forall cps_p, cps p = Some cps_p -> 
      exists cps_v, cps_value v = Some cps_v /\ (
        forall k r, closed_value k -> 
          (app k (cps_v)) ~~>* r -> 
            (app cps_p k) ~~>* r
      ).
Proof.
  induction 1; light; unfold cps, cps_value in *; repeat simp_cps;
  try solve [repeat invert_constructor_equalities || destruct_match || light || options;
  eexists; repeat light; econstructor; t_closer; auto].
  - (* succ *)
    repeat light.
    destruct (is_value t) eqn:E; unfold option_map in H1; destruct_match; 
    repeat light; invert_constructor_equalities.
    + unshelve epose proof bs_unique t v t _ _;
      apply is_value_correct in E; eauto with values.
      repeat rewrite_any; repeat light.
      eexists; repeat light.
      eapply ss_bs.
      econstructor; t_closer.
      repeat light.
      rewrite open_none; solve_wf_cps_rec; auto.
    + unshelve epose proof H2 _ eq_refl; clear H2; steps.
      rewrite_any; eexists; repeat light.
      eapply ss_bs.
      econstructor; t_closer.
      repeat light.
      rewrite open_none; solve_wf_cps_rec.
      apply_any; t_closer.
      eapply ss_bs.
      * econstructor;
        eapply cps_value_of_value; 
        apply bs_value in H; eauto.
      * repeat light.
        rewrite open_none; t_closer.
  - (* lambda *)
    repeat invert_constructor_equalities || destruct_match || light || options.
    eexists; repeat light.
    econstructor; repeat light; try solve [eapply value_bs; t_closer]. light.
    rewrite open_none; auto with bcbv_step.
    apply close_keeps_wf; try lia.
    t_closing;
    eauto using wf_monotone2, cps_rec_wf with wf. 
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
      rewrite open_none; solve_wf_cps_rec.
      rewrite open_none; solve_wf_cps_rec.
      unshelve epose proof IHbcbv_step1 _ _ eq_refl; repeat step;
      t_closer; try solve [
        unfold closed_value; light; eauto with values; eapply bs_closed_term; eauto;
      t_closer].
      apply_any. (* From IHbcbv_step1 *)
      * t_closing;
        solve_pfv_nill_cps_rec;
        solve_wf_cps_rec;
        solve_erased_terms_cps_rec.
      * econstructor; eauto with bcbv_step; repeat light;
        try solve [eapply value_bs; t_closer].
        rewrite open_none; solve_wf_cps_rec.
        rewrite open_none; t_closer.
        apply_any. (* From IHbcbv_step2 *)
        -- t_closing;
          eauto using fv_close_nil2, fv_close_cps_rec;
          eauto 7 using wf_monotone2, close_keeps_wf, cps_rec_wf with wf;
          eauto using is_erased_term_close, cps_rec_outputs_erased_terms.
        -- econstructor; eauto with bcbv_step; repeat light;
          try solve [eapply value_bs; t_closer].
          eapply value_bs. 
          apply cps_of_closed_value_is_value with v2; eauto.
          t_closer.
          rewrite (open_none k); t_closer.
          rewrite open_none;
          try solve [t_closing; 
          eauto 7 using wf_monotone2, close_keeps_wf, cps_rec_wf with wf].
          apply ss_bs with (app (psubstitute cps_t ((0, cps_v) :: nil) term_var) k);
          auto. (* From IHbcbv_step3 *)
          constructor.
          rewrite <- open_close with (k := 0);
          try solve [t_closing; eapply cps_rec_wf; eauto with wf].
          constructor.
          eapply cps_value_of_value; eauto; t_closer.
Qed.

Theorem cps_correct: 
  forall p v, p ~~>* v -> closed_term p -> 
    forall cps_p, cps p = Some cps_p -> 
      exists cps_v, cps_value v = Some cps_v /\
        (app cps_p (notype_lambda (lvar 0 term_var))) ~~>* cps_v.
Proof.
  repeat light.
  unshelve epose proof cps_eval p v _ _ _ _; eauto.
  steps.
  exists cps_v; repeat light.
  apply_any; t_closer.
  econstructor.
  econstructor.
  eapply value_bs; eauto.
  eapply (cps_value_of_value v); eauto with values.
  light.
  apply value_bs.
  eapply (cps_value_of_value v); eauto with values.
Qed.
