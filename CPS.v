Require Import SystemFR.SmallStep.
Require Import SystemFR.Trees.
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
  cps_rec false (fvar i term_var) _ := Some (notype_lambda (app (lvar 0 term_var) (fvar i term_var)));
  cps_rec false uu _ := Some (notype_lambda (app (lvar 0 term_var) uu));
  cps_rec false ttrue _ := Some (notype_lambda (app (lvar 0 term_var) ttrue));
  cps_rec false tfalse _ := Some (notype_lambda (app (lvar 0 term_var) tfalse));
  cps_rec false zero _ := Some (notype_lambda (app (lvar 0 term_var) zero));
  cps_rec false (succ t') nf := 
    if (is_open_value t') then 
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

  cps_rec false (notype_tfix t) nf := None;

  cps_rec false notype_err nf := Some notype_err;
  cps_rec false (ite cond tthen telse) nf := None;

  cps_rec false (pp t1 t2) nf := None;
  cps_rec false (pi1 t) nf := None;
  cps_rec false (pi2 t) nf := None;
  
  (* 
    tmatch t t0 ts => 
      λk. 
        (cps_t (
          λrt. tmatch rt 
                  (cps_t0 k)
                  ((close 0 cps_ts nf) k)
        ))
  *)
  cps_rec false (tmatch t t0 ts) nf := 
    match (cps_rec false t nf), 
      (cps_rec false t0 nf),
      (cps_rec false (open 0 ts (fvar nf term_var)) (S nf)) with
    | Some cps_t, Some cps_t0, Some cps_ts => 
      Some (notype_lambda (
        app cps_t (notype_lambda (
          tmatch (lvar 0 term_var)
            (app cps_t0 (lvar 1 term_var))
            (* because 0 is used by the free variable of the pattern *)
            (app (close 0 cps_ts nf) (lvar 2 term_var))
        ))
      ))
    | _, _, _ => None
    end;
  cps_rec false (sum_match t tl tr) nf := 
    match (cps_rec false t nf),
      (cps_rec false (open 0 tl (fvar nf term_var)) (S nf)),
      (cps_rec false (open 0 tr (fvar nf term_var)) (S nf)) with
    | Some cps_t, Some cps_tl, Some cps_tr =>
      Some (notype_lambda (
        app cps_t (notype_lambda (
          sum_match (lvar 0 term_var)
            (* because 0 is used by the free variable of the pattern *)
            (app (close 0 cps_tl nf) (lvar 2 term_var))
            (app (close 0 cps_tr nf) (lvar 2 term_var))
        ))
      ))
    | _, _, _ => None
    end;
  cps_rec false (tleft t') nf := 
    if (is_open_value t') then 
      option_map 
        (fun cps_v => notype_lambda (app (lvar 0 term_var) (tleft (cps_v))))
        (cps_rec true t' nf)
    else 
      option_map 
        (fun cps_t' => 
          (notype_lambda (
            app (cps_t') (notype_lambda (
              app (lvar 1 term_var) (tleft (lvar 0 term_var))
            ))
          ))
        )
        (cps_rec false t' nf);
  cps_rec false (tright t') nf :=
    if (is_open_value t') then 
      option_map 
        (fun cps_v => notype_lambda (app (lvar 0 term_var) (tright (cps_v))))
        (cps_rec true t' nf)
    else 
      option_map 
        (fun cps_t' => 
          (notype_lambda (
            app (cps_t') (notype_lambda (
              app (lvar 1 term_var) (tright (lvar 0 term_var))
            ))
          ))
        )
        (cps_rec false t' nf);
  cps_rec false (boolean_recognizer r t) nf := None;
  cps_rec false (unary_primitive o t) nf := None;
  cps_rec false (binary_primitive o t1 t2) nf := None;
  cps_rec false (tsize t) nf := None;
  
  cps_rec false _ _ := None;

  (* CPS value *)
  cps_rec true (fvar n term_var) _ := Some (fvar n term_var);
  cps_rec true uu _ := Some uu;
  cps_rec true ttrue _ := Some ttrue;
  cps_rec true tfalse _ := Some tfalse;
  cps_rec true (pp e1 e2) _ := None;
  cps_rec true (tleft e) nf := option_map tleft (cps_rec true e nf);
  cps_rec true (tright e) nf := option_map tright (cps_rec true e nf);
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

Ltac cps_rec_def := 
  program_simplify; CoreTactics.equations_simpl;
  try program_solve_wf;
  try solve [rewrite open_t_size; lia]; lia.

Solve Obligations with cps_rec_def.
Fail Next Obligation.

Definition cps (t : tree) := cps_rec false t 0.

Definition cps_value (t : tree) := cps_rec true t 0.

(* Eval compute in (cps_rec false (tmatch zero (succ zero) (lvar 0 term_var)) 0).

Eval compute in (
  option_map 
    option_map 
  option_map 
    (fun cps_t => eval (app cps_t (notype_lambda (lvar 0 term_var))) 2)
    (cps (tmatch zero (succ zero) (lvar 0 term_var)))
). *)

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
  repeat light || simp_cps || options || destruct_match 
  || destruct_tag || instantiate_any.
Qed.

Hint Resolve cps_not_def_cps_value_not_def : cps.

Lemma cps_of_value: forall v nf, is_open_value v = true -> 
  cps_rec false v nf = 
  option_map 
    (fun cps_value_v => notype_lambda (app (lvar 0 term_var) cps_value_v))
    (cps_rec true v nf).
Proof.
  induction v;
  repeat light || simp_cps || options
  || invert_constructor_equalities || destruct_match.
Qed.

Hint Resolve cps_of_value : cps.

Ltac instantiate_cps_of_value :=
  match goal with
  | H: is_open_value ?t = true,
    H': cps_rec ?value ?t ?nf = Some _ |- _ =>
    poseNew (Mark t "cps_of_value");
    unshelve epose proof cps_of_value t nf _; 
    eauto with open_value cps 
  | H: cbv_value ?t,
    H': cps_rec ?value ?t ?nf = Some _ |- _ =>
    poseNew (Mark t "cps_of_value");
    unshelve epose proof cps_of_value t nf _; 
    eauto with open_value cps
  end.

Lemma cps_of_value_is_open_value : forall p cps_p nf,
  cps_rec true p nf = Some cps_p -> is_open_value cps_p = true.
Proof.
  induction p; try destruct_tag; 
  repeat light || simp_cps || options 
  || destruct_match || invert_constructor_equalities;
  eauto.
Qed.

Hint Resolve cps_of_value_is_open_value : cps. 
(* Lemma cps_of_value: forall v cps_v nf, 
  is_open_value v = true -> cps_rec false v nf = Some cps_v -> exists cps_value_v, 
    cps_rec true v nf = Some cps_value_v /\ 
    (notype_lambda (app (lvar 0 term_var) cps_value_v)) = cps_v.
Proof.
  induction v; 
  repeat light || simp_cps || options  
  || invert_constructor_equalities || destruct_match; 
  eauto.
Qed.

Lemma cps_of_value': forall v cps_value_v nf, 
  is_open_value v = true -> cps_rec true v nf = Some cps_value_v -> 
    cps_rec false v nf = Some (notype_lambda (app (lvar 0 term_var) cps_value_v)).
Proof.
  induction v; 
  repeat light || options || destruct_match || t_equality
   || invert_constructor_equalities || simp_cps.
Qed. *)

(* Hint Resolve cps_of_value cps_of_value' : cps. *)

Definition is_variable (t : tree) nf : Prop := 
  match t with
  | fvar i term_var => i < nf
  | _ => False
  end.

Lemma sub_wfs: forall sub nf, 
  (forall s, s ∈ (range sub) -> is_variable s nf) -> 
    wfs sub 0.
Proof.
  induction sub;
  repeat light || destruct_match || unfold is_variable in *.
  - unshelve epose proof H t _; repeat light || destruct_match.
  - eapply_any; repeat light.
    unshelve epose proof H s _; repeat light. eauto.
Qed.

Hint Resolve sub_wfs: wf.

Lemma is_variable_monotonic: forall t nf, 
  is_variable t nf -> is_variable t (S nf).
Proof.
  unfold is_variable; repeat light || destruct_match.
Qed.

Hint Resolve is_variable_monotonic : open_value.

Lemma is_variable_is_open_value: forall s nf,
  is_variable s nf -> is_open_value s = true.
Proof.
  unfold is_variable; repeat light || destruct_match.
Qed.

Lemma is_variables_is_open_value: forall nf ls,
  (forall s', s' ∈ ls -> is_variable s' nf) ->
  forall s, s ∈ ls -> is_open_value s = true.
Proof.
  eauto using is_variable_is_open_value.
Qed.

Hint Resolve is_variable_is_open_value is_variables_is_open_value : open_value.

(* Ltac rewrite_IH_subst_nf IHsize_t nf :=
  match goal with 
  | H : cps_rec false (psubstitute ?t ?sub term_var) ?nf' = Some ?t' |- _ => 
    poseNew (Mark (sub, t) "subst"); rewrite (IHsize_t _ _ nf) in H
  end. *)

Lemma substitute_close2: forall t k nf nf' sub, nf < nf' ->
  (forall s, s ∈ (range sub) -> is_variable s nf') ->
  (forall x, x ∈ (support sub) -> x < nf) ->
  (forall n, n ∈ (pfv t term_var) -> n < nf') ->
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

Hint Resolve substitute_close2 : close.

Lemma open_keeps_wf: forall t i n nf, wf t n -> wf (open i t (fvar nf term_var)) n.
Proof.
  induction t; light; steps.
Qed.

Lemma close_keeps_wf: forall t nf i n, 
  wf t n -> i < n -> wf (close i t nf) n.
Proof.
  induction t; light; 
  auto with step_tactic lia.
Qed.

Hint Resolve open_keeps_wf close_keeps_wf : wf.

Ltac instantiate_IH_cps_rec_outputs_erased_terms' IH :=
  match goal with
  | H: cps_rec _ _ _ = Some _ |- _ =>
      unshelve epose proof IH _ _ _ _ H _;
      clear H; 
      eauto with lia erased
  end.

Lemma cps_rec_outputs_erased_terms': forall size_t t nf cps_t value,
  cps_rec value t nf = Some cps_t -> tree_size t < size_t -> is_erased_term cps_t.
Proof.
  induction size_t; try lia; destruct t; destruct value; 
  repeat light || simp_cps || destruct_match 
  || invert_constructor_equalities || options 
  || destruct_tag
  || instantiate_IH_cps_rec_outputs_erased_terms' IHsize_t;
  rewrite open_t_size;
  eauto with lia.
Qed.

Lemma cps_rec_outputs_erased_terms: forall t nf cps_t value,
  cps_rec value t nf = Some cps_t -> is_erased_term cps_t.
Proof.
  eauto using cps_rec_outputs_erased_terms'.
Qed.

Ltac instantiate_cps_rec_erased :=
  match goal with
  | H: cps_rec _ _ _ = Some _ |- _ => 
    poseNew (Mark H "cps_rec_erased");
    unshelve epose proof cps_rec_outputs_erased_terms _ _ _ _ H;
    t_closer
  end.

Hint Resolve cps_rec_outputs_erased_terms : cps.

Ltac apply_IH_cps_rec_wf' IH :=
  match goal with 
  | H: cps_rec _ ?t ?nf = Some ?t' |- _ => 
    unshelve epose proof IH _ _ _ _ _ _ H; clear H
  end.

Lemma cps_rec_wf': forall size_t t nf cps_t value,
  tree_size t < size_t -> 
    wf t 0 -> cps_rec value t nf = Some cps_t ->
      wf cps_t 0.
Proof.
  induction size_t; repeat light; try lia;
  destruct t; destruct value; try destruct_tag; simp_cps; 
  repeat light || destruct_match 
  || invert_constructor_equalities || apply_IH_cps_rec_wf' IHsize_t 
  || rewrite open_t_size || options;
  eauto with lia wf step_tactic.
Qed.

Lemma cps_rec_wf: forall t nf cps_t value,
  cps_rec value t nf = Some cps_t -> wf t 0 -> 
    wf cps_t 0.
Proof.
  eauto using cps_rec_wf'.
Qed.

Ltac instantiate_cps_rec_wf := 
  match goal with
  | H: cps_rec _ ?t _ = Some ?t',
    H': wf ?t 0 |- _ => 
      poseNew (Mark H "cps_rec_wf");
      unshelve epose proof cps_rec_wf _ _ _ _ H H'
  | H: cps_rec _ ?t _ = Some ?t',
    H': closed_term ?t |- _ => 
    poseNew (Mark H "cps_rec_wf");
    unshelve epose proof cps_rec_wf _ _ _ _ H _; t_closer
  | H: cps_rec _ ?t _ = Some ?t',
    H': closed_value ?t |- _ => 
    poseNew (Mark H "cps_rec_wf");
    unshelve epose proof cps_rec_wf _ _ _ _ H _; t_closer    
  end.

Ltac rewrite_open_none := 
  repeat rewrite open_none;
  try solve [
    repeat instantiate_cps_rec_wf; 
    eauto using wf_monotone2 with wf
  ].

Hint Resolve cps_rec_wf : cps.

Ltac apply_IH_cps_rec_pfv' IH :=
  match goal with 
  | H: cps_rec _ ?t ?nf = Some ?t',
    H': ?x ∈ (pfv ?t' term_var) |- _ => 
    unshelve epose proof IH t _ nf t' x _ H _ eq_refl _ _; clear H
  end.

Lemma cps_rec_pfv': forall size_t t fvs nf t' x value,
  cps_rec value t nf = Some t' ->
  tree_size t < size_t -> pfv t term_var = fvs -> 
  (forall n, n ∈ fvs -> n < nf) ->
    x ∈ (pfv t' term_var) -> x ∈ fvs.
Proof.
  induction size_t; light; try lia.
  destruct t eqn:E; destruct value;
  repeat light || simp_cps_hyp || destruct_match || destruct_tag
  || invert_constructor_equalities || list_utils 
  || apply_IH_cps_rec_pfv' IHsize_t
  || rewrite open_t_size || fv_close || fv_open || options;
  try lia.
Qed.

Lemma cps_rec_pfv: forall t fvs nf t' x value,
  cps_rec value t nf = Some t' ->
  pfv t term_var = fvs ->
  (forall n, n ∈ fvs -> n < nf) ->
    x ∈ (pfv t' term_var) -> x ∈ fvs.
Proof.
  eauto using cps_rec_pfv'.
Qed.

Lemma cps_rec_pfv_nil: forall t nf cps_t value,
  pfv t term_var = nil -> cps_rec value t nf = Some cps_t -> pfv cps_t term_var = nil.
Proof.
  light.
  destruct (pfv cps_t term_var) eqn:E; auto.
  unshelve epose proof cps_rec_pfv t nil nf cps_t n _ _ _ _ _; 
  repeat light; try lia.
  rewrite E.
  repeat light.
Qed.

Hint Resolve cps_rec_pfv cps_rec_pfv_nil : cps.

Ltac instantiate_cps_rec_pfv := 
  match goal with
  | H: cps_rec _ ?t _ = Some _,
    H': pfv ?t term_var = nil |- _ => 
      poseNew (Mark (H, H') "cps_rec_pfv_nill");
      unshelve epose proof cps_rec_pfv_nil _ _ _ _ H' H
  | H: cps_rec _ _ _ = Some ?t,
    H': ?n ∈ pfv ?t term_var |- _ =>
      poseNew (Mark (H, H') "cps_rec_pfv");
      unshelve epose proof cps_rec_pfv _ _ _ _ _ _ H eq_refl _ H';
      repeat light || fv_open || list_utils || destruct_match;
      eauto with cps; try lia
  end.

(* Lemma cps_value_of_open_value: forall v cps_v, 
  is_open_value v = true -> cps_value v = Some cps_v -> is_open_value cps_v = true.
Proof.
  unfold cps_value; light; generalize dependent cps_v; induction H;
  repeat simp_cps || options || destruct_match || invert_constructor_equalities || light;
  eauto with values.
Qed. *)

(* Lemma cps_value_wf: forall v cps_v,
  wf v 0 -> cps_value v = Some cps_v -> wf cps_v 0.
Proof.
  eauto using cps_rec_wf.
Qed. *)

(* Lemma cps_value_pfv_nill: forall t cps_t,
  pfv t term_var = nil -> cps_value t = Some cps_t -> pfv cps_t term_var = nil.
Proof.
  eauto using cps_rec_pfv_nil.
Qed. *)

(* Lemma cps_value_is_earased: forall v cps_v,
  is_erased_term v -> cps_value v = Some cps_v -> is_erased_term cps_v.
Proof.
  eauto using cps_rec_outputs_erased_terms.
Qed. *)

Lemma cps_rec_open_value: forall v cps_v value nf,
  is_open_value v = true -> 
  cps_rec value v nf = Some cps_v -> 
    is_open_value cps_v = true.
Proof.
  induction v; destruct value; 
  repeat light || simp_cps || destruct_tag || invert_constructor_equalities
  || options || destruct_match;
  eauto.
Qed.

Hint Resolve cps_rec_open_value : cps.

Ltac instantiate_cps_rec_open_value := 
  match goal with
  | H: cps_rec _ ?t _ = Some _,
    H': is_open_value ?t = true |- _ => 
      poseNew (Mark (H, H') "cps_rec_open_value");
      unshelve epose proof cps_rec_open_value _ _ _ _ H' H
  | H: cps_rec _ ?t _ = Some _,
    H': cbv_value ?t |- _ => 
      poseNew (Mark (H, H') "cps_rec_open_value");
      unshelve epose proof cps_rec_open_value _ _ _ _ _ H;
      eauto with open_value
  end.

Lemma cps_rec_closed_value_is_value: forall v cps_v value nf,
  closed_value v -> cps_rec value v nf = Some cps_v -> closed_value cps_v.
Proof.
  t_closing;
  eauto with cps open_value.
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

Hint Resolve fv_close_cps_rec : cps.

(* Lemma substitute_value: forall t sub tag,
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
  (forall n, n ∈ (pfv t term_var) -> n < nf) -> 
  (forall s, s ∈ (range sub) -> is_variable s nf') ->
  (forall x, x ∈ (support sub) -> x < nf) ->
    cbv_value (psubstitute t sub tag) -> cbv_value t.
Proof.
  induction t; repeat light; eauto with values; inversion H3;
  repeat light || destruct_match || destruct_tag || 
  t_lookup || instantiate_any || constructor;
  eapply_any; eauto; repeat light; apply H0; repeat light || list_utils.
Qed.

Lemma substitute_vars_not_is_value': forall t sub tag nf nf', nf < nf'->
  (forall n, n ∈ (pfv t term_var) -> n < nf) -> 
  (forall s, s ∈ (range sub) -> is_variable s nf') ->
  (forall x, x ∈ (support sub) -> x < nf) ->
    is_value (psubstitute t sub tag) = true -> is_value t = true.
Proof.
  repeat light;
  apply is_value_correct in H3. apply is_value_correct.
  eauto using substitute_vars_not_value.
Qed.

Lemma substitute_vars_not_is_value: forall t sub tag nf nf', 
  is_value t = false -> 
  nf < nf'->
  (forall n, n ∈ (pfv t term_var) -> n < nf) -> 
  (forall s, s ∈ (range sub) -> is_variable s nf') ->
  (forall x, x ∈ (support sub) -> x < nf) ->
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
  end. *)

(* Lemma substitute_value: forall t sub tag,
  cbv_value t -> cbv_value (psubstitute t sub tag).
Proof.
  induction 1; repeat light; eauto with values.
Qed. *)

Lemma substitute_is_open_value: forall t sub tag,
  (forall s, s ∈ (range sub) -> is_open_value s = true) ->
    is_open_value t = true -> is_open_value (psubstitute t sub tag) = true.
Proof.
  induction t;
  repeat light || destruct_match || t_lookup || bools.
Qed.

Lemma substitute_is_not_open_value_contra: forall t sub,
  (forall s, s ∈ (range sub) -> is_open_value s = true) ->
    is_open_value (psubstitute t sub term_var) = true -> is_open_value t = true.
Proof.
  induction t;
  repeat light || destruct_match || bools || instantiate_any.
Qed.

Lemma substitute_is_not_open_value: forall t sub,
  (forall s, s ∈ (range sub) -> is_open_value s = true) ->
  is_open_value t = false -> 
    is_open_value (psubstitute t sub term_var) = false.
Proof.
  light.
  destruct_is_open_value;
  repeat light.
  eapply_anywhere substitute_is_not_open_value_contra; eauto.
Qed.

Ltac apply_subst_is_value sub :=
  match goal with 
  | H: is_open_value ?t = true |- _ => 
    unshelve epose proof substitute_is_open_value _ sub term_var _ H;
    eauto with open_value; try rewrite_any
  | H: is_open_value ?t = false |- _ => 
    unshelve epose proof substitute_is_not_open_value _ sub _ H;
    eauto with open_value; try rewrite_any
  end.

Ltac destruct_apply_subst_is_value := 
  match goal with
  | [|- context[is_open_value (psubstitute ?t ?sub term_var)]] =>
    let is_open_value_eqn := fresh "is_open_value_eqn" in
    destruct (is_open_value t) eqn:is_open_value_eqn;
    apply_subst_is_value sub; 
    repeat light || t_lookup; 
    try solve [t_closing; eauto with lia open_value]
  end.

Hint Resolve substitute_is_open_value substitute_is_not_open_value : open_value.

(* Lemma substitute_vars_not_value: forall t sub nf,
  (forall s, s ∈ (range sub) -> is_variable s nf) ->
    is_open_value (psubstitute t sub term_var) = true -> is_open_value t = true.
Proof.
  induction t;
  repeat light || destruct_match || bools || instantiate_any.
Qed.

Lemma substitute_vars_not_is_open_value: forall t sub nf, 
  is_open_value t = false -> 
  (forall s, s ∈ (range sub) -> is_variable s nf) ->
    is_open_value (psubstitute t sub term_var) = false.
Proof.
  repeat light.
  destruct (is_open_value (psubstitute t sub term_var)) eqn:E; auto.
  eapply_anywhere substitute_vars_not_value; eauto.
Qed. *)

Ltac apply_IH_cps_rec_subst_nf' IH := 
  match goal with
  | H: forall n, n ∈ pfv ?t term_var -> S n <= ?nf |- 
    context[cps_rec ?value (psubstitute ?t ?sub term_var) ?nf'] =>
      poseNew (Mark (H, t) "apply IH");
      unshelve epose proof IH t sub (nf) (nf') value _ _ _ _ _;
      repeat light || list_utils || rewrite open_t_size || fv_open
      || destruct_match || invert_constructor_equalities || t_equality;
      eauto using is_variable_monotonic with lia
  | H: forall n, n ∈ pfv _ term_var -> S n <= ?nf |- 
    context[cps_rec ?value (psubstitute ?t ?sub term_var) ?nf'] =>
      poseNew (Mark (H, t) "apply IH");
      unshelve epose proof IH t sub (S nf) (nf') value _ _ _ _ _;
      repeat light || list_utils || rewrite open_t_size || fv_open
      || destruct_match || invert_constructor_equalities || t_equality;
      eauto using is_variable_monotonic with lia
  | H: forall n, n ∈ pfv ?t term_var ++ pfv ?t' term_var -> S n <= ?nf |- 
    context[cps_rec ?value (psubstitute _ ?sub term_var) ?nf'] =>
      poseNew (Mark (H) "apply IH");
      unshelve epose proof IH t sub (nf) (nf') value _ _ _ _ _;
      unshelve epose proof IH t' sub (nf) (nf') value _ _ _ _ _;
      repeat light || list_utils || rewrite open_t_size || fv_open
      || destruct_match || invert_constructor_equalities || t_equality;
      eauto using is_variable_monotonic with lia
  | H: forall n, n ∈ pfv ?t1 term_var ++ pfv ?t2 term_var ++ pfv ?t3 term_var -> 
        S n <= ?nf |-
    context[cps_rec ?value (psubstitute ?t2 ?sub term_var) ?nf'] => 
      poseNew (Mark H "apply IH");
      unshelve epose proof IH t1 sub (nf) (nf') value _ _ _ _ _;
      unshelve epose proof IH t2 sub (nf) (nf') value _ _ _ _ _;
      unshelve epose proof IH 
        (open 0 t3 (fvar nf term_var)) ((nf, fvar nf' term_var) :: sub) 
        (S nf) (S nf') value _ _ _ _ _;
      repeat light || list_utils || rewrite open_t_size || fv_open
      || destruct_match || invert_constructor_equalities || t_equality;
      eauto using is_variable_monotonic with lia
  | H: forall n, n ∈ pfv ?t1 term_var ++ pfv ?t2 term_var ++ pfv ?t3 term_var -> 
          S n <= ?nf |-
      context[cps_rec ?value (psubstitute ?t1 ?sub term_var) ?nf'] => 
        poseNew (Mark H "apply IH");
        unshelve epose proof IH t1 sub (nf) (nf') value _ _ _ _ _;
        unshelve epose proof IH 
          (open 0 t2 (fvar nf term_var)) ((nf, fvar nf' term_var) :: sub) 
          (S nf) (S nf') value _ _ _ _ _;
        unshelve epose proof IH 
          (open 0 t3 (fvar nf term_var)) ((nf, fvar nf' term_var) :: sub) 
          (S nf) (S nf') value _ _ _ _ _;
        repeat light || list_utils || rewrite open_t_size || fv_open
        || destruct_match || invert_constructor_equalities || t_equality;
        eauto using is_variable_monotonic with lia
  end.

Lemma cps_rec_subst_nf': forall size_t t sub nf nf' value, 
  tree_size t < size_t -> nf < nf' ->
  (forall n, n ∈ (pfv t term_var) -> n < nf) -> 
  (forall s, s ∈ (range sub) -> is_variable s nf') ->
  (forall x, x ∈ (support sub) -> x < nf) ->
    cps_rec value (substitute t sub) nf' = 
    option_map (fun res => substitute res sub)
    (cps_rec value t nf).
Proof.
  induction size_t; try lia.
  destruct t; destruct value;
  repeat light || simp_cps || invert_constructor_equalities 
  || t_equality || options || destruct_tag;
  try solve [unfold is_variable in *; 
  repeat light || simp_cps || invert_constructor_equalities 
  || t_equality || destruct_match || t_lookup || instantiate_any];
  try solve [try destruct_apply_subst_is_value;
  repeat apply_IH_cps_rec_subst_nf' IHsize_t; try lia; 
  repeat light || list_utils 
  || destruct_match || invert_constructor_equalities || t_equality];
  try solve [
    repeat erewrite <- substitute_open3 with (x := nf); 
    eauto with wf; try solve [
      repeat light || list_utils 
      || instantiate_any;
      lia
    ];
    apply_IH_cps_rec_subst_nf' IHsize_t;
    apply substitute_close2; 
    eauto with lia; light;
    instantiate_cps_rec_pfv;
    instantiate_any; lia
  ].
Qed.

Lemma cps_rec_subst_nf: forall t value sub nf nf',
  nf < nf' ->
  (forall n, n ∈ (pfv t term_var) -> n < nf) -> 
  (forall s, s ∈ (range sub) -> is_variable s nf') ->
  (forall x, x ∈ (support sub) -> x < nf) ->
    cps_rec value (substitute t sub) nf' = 
    option_map (fun res => substitute res sub)
    (cps_rec value t nf).
Proof.
  eauto using cps_rec_subst_nf'.
Qed.

Lemma cps_rec_nf: forall t nf nf' value, 
  (forall n, n ∈ (pfv t term_var) -> n < nf) -> 
  (forall n, n ∈ (pfv t term_var) -> n < nf') -> 
    cps_rec value t nf = cps_rec value t nf'.
Proof.
  light.
  destruct (Compare_dec.lt_eq_lt_dec nf nf') as [[E | E] | E]; auto.
  - (* nf < nf' *)
    unshelve epose proof cps_rec_subst_nf t value nil nf nf' _ _ _ _; auto;
    repeat light || options || destruct_match || rewrite substitute_nothing3 in *.
  - (* nf > nf' *)
    unshelve epose proof cps_rec_subst_nf t value nil nf' nf _ _ _ _; auto;
    repeat light || options || destruct_match || rewrite substitute_nothing3 in *.
Qed.

Hint Rewrite cps_rec_nf : cps.

Ltac rewrite_with_cps_rec_nf :=
  match goal with
  | H: pfv ?t term_var = nil,
    H': cps_rec ?value ?t ?nf = Some _ |- _ => 
      rewrite (cps_rec_nf t nf 0 value) in *; 
      repeat light || list_utils
  | H: pfv ?t term_var = nil |- cps_rec ?value ?t ?nf = Some _ =>
      rewrite (cps_rec_nf t nf 0 value) in *;
      repeat light || list_utils
  end.

(* Lemma cps_rec_closed_term_nf': forall size_t t,
  tree_size t < size_t ->
  forall value nf nf',
  pfv t term_var = nil -> 
    cps_rec value t nf = cps_rec value t nf'.
Proof.
  induction size_t; try lia; destruct t; destruct value; try destruct_tag;
  repeat light || simp_cps || destruct_match || invert_constructor_equalities
  || t_equality || options.

  induction t; try destruct_tag; destruct value; 
  repeat light || simp_cps || options || t_equality 
  || destruct_match || invert_constructor_equalities.
  repeat apply_anywhere cps_rec_pfv_nil.
Qed. *)

(* Lemma cps_rec_closed_term_nf: forall t value nf nf',
  pfv t term_var = nil -> cps_rec value t nf = cps_rec value t nf'.
Proof.
  induction t; try destruct_tag; destruct value; 
  repeat light || simp_cps || options || t_equality 
  || destruct_match || invert_constructor_equalities.
  repeat apply_anywhere cps_rec_pfv_nil. 
Qed.*)

Ltac apply_IH_cps_rec_subst IH := 
  match goal with
  | [|- context[cps_rec ?value (psubstitute ?t ((?x, ?v) :: nil) term_var) ?nf]] =>
    poseNew (Mark (value, t, x, v, nf) "apply_IH_cps_rec_subst");
    unshelve epose proof IH t nf value _ _ _;
    repeat light || fv_open || list_utils || rewrite open_t_size
    || invert_constructor_equalities;
    try solve [repeat light || destruct_match; lia]
  end.

Lemma cps_rec_subst: forall v cps_v x, 
  closed_value v -> cps_rec true v 0 = Some cps_v -> forall p_size p nf value,
  tree_size p < p_size -> x < nf ->
  (forall n, n ∈ (pfv p term_var) -> n < nf) ->
    cps_rec value (substitute p ((x, v)::nil)) nf = 
    option_map (fun cps_p => substitute cps_p ((x, cps_v)::nil)) (cps_rec value p nf) .
Proof.
  induction p_size; try lia; destruct p; destruct value; repeat light || simp_cps;
  try solve [t_closing;
    repeat light || simp_cps || destruct_match || destruct_tag || options
    || invert_constructor_equalities || t_equality || step_inversion cbv_value
    || instantiate_cps_of_value || rewrite_with_cps_rec_nf];
  try solve [
    repeat light || simp_cps || apply_IH_cps_rec_subst IHp_size || options
    || invert_constructor_equalities || t_equality || list_utils || destruct_match
  ]; try solve [
    destruct_apply_subst_is_value; apply_IH_cps_rec_subst IHp_size;
    repeat light || options || simp_cps || invert_constructor_equalities 
    || t_equality || destruct_match
  ]; try solve [
    repeat rewrite substitute_open2 in *; repeat light || t_closer 
    || invert_constructor_equalities || t_equality;
    try solve [repeat destruct_match || light; lia];
    repeat apply_IH_cps_rec_subst IHp_size;
    repeat light || options || destruct_match 
    || invert_constructor_equalities || t_equality;
    rewrite substitute_close; repeat light; try lia;
    t_closing; eauto with cps
  ].
Qed.

Lemma cps_subst: forall v cps_v x nf, 
  closed_value v -> cps_value v = Some cps_v -> forall p value, x < nf ->
  (forall n, n ∈ (pfv p term_var) -> n < nf) ->
    cps_rec value (substitute p ((x, v)::nil)) nf = 
    option_map (fun cps_p => substitute cps_p ((x, cps_v)::nil)) (cps_rec value p nf).
Proof.
  eauto using cps_rec_subst.
Qed.

Hint Resolve cps_subst : cps.

Lemma cps_value_def_for_values: forall v, 
  cbv_value v -> exists cps_v, cps_value v = Some cps_v.
Proof.
Admitted.

Lemma cps_rec_defined_for_erased_wf_terms: forall t nf, 
  wf t 0 -> is_erased_term t -> exists cps_t, cps_rec false t nf = Some cps_t.
Proof.
Admitted.

Lemma cps_defined_for_erased_wf_terms: forall t, 
  wf t 0 -> is_erased_term t -> exists cps_t, cps t = Some cps_t.
Proof.
  eauto using cps_rec_defined_for_erased_wf_terms.
Qed.

#[global]
Hint Resolve cps_defined_for_erased_wf_terms cps_rec_defined_for_erased_wf_terms: cps.

Ltac solve_wf_cps_rec :=
  try solve [try apply wf_monotone2; eapply cps_rec_wf; eauto; t_closer];
  try solve [t_closing; eauto using wf_monotone2 with cps wf].

Ltac solve_pfv_nill_cps_rec :=
  try solve [eapply cps_rec_pfv_nil; eauto].

Ltac solve_erased_terms_cps_rec :=
  try solve [
    try eapply is_erased_term_close;
    eapply cps_rec_outputs_erased_terms; eauto].

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
  try solve [
    repeat invert_constructor_equalities || destruct_match || light || options;
    eexists; repeat light; econstructor; t_closer; auto
  ].
  - (* succ *)
    options; destruct_is_open_value; 
    repeat light || invert_constructor_equalities.
    + unshelve epose proof bs_unique t v t _ _; 
      try solve [
        t_closing; 
      t_closing;
        t_closing; 
        eauto using value_bs with values open_value
      ].
      repeat light || rewrite_any 
      || destruct_match || invert_constructor_equalities.
      eexists; repeat light; t_closing.
      eapply ss_bs; [econstructor | idtac]; 
      repeat light. 
      rewrite_open_none.
    + repeat light || invert_constructor_equalities 
      || destruct_match;
      unshelve epose proof H2 _ eq_refl; steps.
      eexists; repeat light.
      eapply ss_bs; [econstructor | idtac]; 
      repeat light; t_closing.
      rewrite_open_none.
      apply_any; t_closer.
      remember H as H'; clear HeqH'.
      apply bs_closed_term in H; t_closing.
      apply bs_value in H'.
      repeat instantiate_cps_rec_pfv.
      instantiate_cps_rec_open_value.
      eapply ss_bs; [econstructor | idtac];
      eauto with open_value cps.
      repeat light.
      rewrite_open_none.
  - (* tmatch zero _ _ *)
    repeat invert_constructor_equalities || destruct_match || light || options || step.
    unshelve epose proof IHbcbv_step1 _ _ eq_refl; t_closer; steps.
    unshelve epose proof IHbcbv_step2 _ _ eq_refl; t_closer; steps.
    rewrite_any.
    eexists; repeat light.
    eapply ss_bs.
    econstructor; t_closer.
    repeat light.
    rewrite_open_none; solve_wf_cps_rec.
    apply_any. 
    + t_closing; 
      eauto with cps;
      solve_wf_cps_rec;
      eauto with cps erased.
      eauto using fv_close_nil2, fv_close_cps_rec.
    + eapply ss_bs.
      econstructor; t_closer.
      repeat light.
      rewrite_open_none;
      solve_wf_cps_rec.
      econstructor; eauto with bcbv_step; repeat light.
  - (* tmatch (succ v) _ _ *) 
    unshelve epose proof cps_rec_defined_for_erased_wf_terms (open 0 ts (fvar 0 term_var)) 1 _ _.
    apply wf_open; t_closer.
    apply is_erased_open; t_closer.
    apply bs_closed_term in H; t_closer.
    apply bs_closed_term in H0; t_closer.
    unshelve epose proof cps_value_def_for_values v' _; t_closer.
    steps.
    eexists; repeat light; eauto with cps.
    eapply ss_bs.
    econstructor; t_closer.
    repeat light.
    rewrite_open_none; solve_wf_cps_rec.
    unshelve epose proof IHbcbv_step1 _ _ eq_refl; t_closer.
    steps.
    repeat light || options || destruct_match || invert_constructor_equalities.
    unshelve epose proof cps_rec_closed_value_is_value _ _ _ _ _ matched2;
    try solve [
      t_closing; 
      step_inversion cbv_value;
      eauto
    ].
    apply_any; try solve [
      t_closing;
      repeat instantiate_cps_rec_pfv;
      repeat instantiate_cps_rec_wf;
      eauto using fv_close_cps_rec, fv_close_nil2 with cps wf;
      solve_wf_cps_rec;
      solve_erased_terms_cps_rec
    ].
    eapply ss_bs.
    econstructor; t_closer.
    repeat light.
    rewrite_open_none; solve_wf_cps_rec.
    eapply BSmatchS.
    + constructor.
      apply value_bs.
      t_closer.
    + repeat light.
      rewrite open_close; solve_wf_cps_rec.
      rewrite_open_none; solve_wf_cps_rec.
      unshelve epose proof cps_subst _ _ 0 1 _ matched2 
        (open 0 ts (fvar 0 term_var)) false _ _;
      t_closer;
      repeat light || fv_open || list_utils || destruct_match;
      try solve [
        t_closing;
        step_inversion cbv_value;
        eauto
      ].
      repeat light || options || destruct_match || invert_constructor_equalities.
      rewrite substitute_open3 in *; t_closer.
      t_substitutions.
      rewrite (cps_rec_nf (open 0 ts v) 1 0 false) in *;
      repeat light || fv_open || list_utils || destruct_match; t_closer.
      unshelve epose proof IHbcbv_step2 _ _ H6; t_closer; steps.
      apply_any; t_closer.
      unfold cps_value in *.
      repeat light.
  - (* lambda *)
    repeat invert_constructor_equalities || destruct_match || light || options.
    eexists; repeat light; t_closing.
    econstructor; 
    try solve [eapply value_bs; t_closer];
    repeat light.
    rewrite open_none;
    eauto using wf_monotone2, cps_rec_wf with bcbv_step wf lia.
  - (* app *)
    unshelve epose proof bs_closed_term _ _ H _;
    unshelve epose proof bs_closed_term _ _ H0 _; t_closer.
    repeat light.

    unshelve epose proof cps_rec_defined_for_erased_wf_terms (open 0 b1 (fvar 0 term_var)) 1 _ _.
    apply wf_open; t_closer.
    apply is_erased_open; t_closer.

    repeat invert_constructor_equalities|| destruct_match || light || options || step.
    unshelve epose proof IHbcbv_step2 _ _ eq_refl; repeat step; 
    try solve [
      unfold closed_value; light; eauto with values; 
      eapply bs_closed_term; eauto;
      t_closer
    ]; t_closer.

    unshelve epose proof IHbcbv_step3 _ (substitute cps_t ((0, cps_v)::nil)) _;
    t_closer.
    + unshelve epose proof cps_subst _ _ 0 1 _ H6 (open 0 b1 (fvar 0 term_var)) false _ _; 
      repeat light; try lia; eauto with values.
      * repeat light || list_utils || fv_open; t_closer.
      * rewrite substitute_open3 in *; t_closer.
        t_substitutions.
        rewrite matched2 in *; repeat light.
        rewrite (cps_rec_nf _ _ 0) in H3; repeat light || fv_open; t_closer.
    + repeat step.
      eexists; light; eauto.
      econstructor; eauto with bcbv_step; repeat light;
      try solve [eapply value_bs; t_closer].
      rewrite_open_none; solve_wf_cps_rec.
      unshelve epose proof IHbcbv_step1 _ _ eq_refl; repeat step;
      t_closer; try solve [
        unfold closed_value; light; eauto with values; 
        eapply bs_closed_term; eauto; t_closer
      ].
      apply_any. (* From IHbcbv_step1 *)
      * t_closing;
        eauto using wf_monotone2 with cps.
      * econstructor; eauto with bcbv_step; repeat light;
        try solve [eapply value_bs; t_closer].
        rewrite_open_none; solve_wf_cps_rec.
        apply_any. (* From IHbcbv_step2 *)
        -- t_closing;
          eauto using fv_close_nil2, fv_close_cps_rec;
          eauto 7 using wf_monotone2, close_keeps_wf, cps_rec_wf with wf;
          eauto using is_erased_term_close, cps_rec_outputs_erased_terms.
        -- econstructor; eauto with bcbv_step; repeat light;
          try solve [eapply value_bs; t_closer].
          eapply value_bs.
          try solve [
            t_closing;
            repeat instantiate_cps_rec_pfv;
            apply bs_value in H0;
            repeat instantiate_cps_rec_open_value
          ].
          rewrite_open_none;
          try solve [
            t_closing; 
            eauto 7 using wf_monotone2, close_keeps_wf, cps_rec_wf with wf
          ].
          apply ss_bs with (app (psubstitute cps_t ((0, cps_v) :: nil) term_var) k);
          auto. (* From IHbcbv_step3 *)
          constructor.
          rewrite <- open_close with (k := 0);
          try solve [t_closing; eapply cps_rec_wf; eauto with wf].
          constructor.
          eauto with cps.
          t_closing.
          repeat apply_anywhere bs_value;
          repeat apply_anywhere cbv_value_is_open_value_true;
          repeat instantiate_cps_rec_pfv;
          repeat instantiate_cps_rec_open_value;
          eapply no_free_var_open_value_is_value;
          eauto.
  - (* tleft *)
    options; destruct_is_open_value; 
    repeat light || invert_constructor_equalities.
    + unshelve epose proof bs_unique t v t _ _; 
      try solve [
        t_closing; 
      t_closing;
        t_closing; 
        eauto using value_bs with values open_value
      ].
      repeat light || rewrite_any 
      || destruct_match || invert_constructor_equalities.
      eexists; repeat light; t_closing.
      eapply ss_bs; [econstructor | idtac]; 
      repeat light. 
      rewrite_open_none.
    + repeat light || invert_constructor_equalities 
      || destruct_match;
      unshelve epose proof H2 _ eq_refl; steps.
      eexists; repeat light.
      eapply ss_bs; [econstructor | idtac]; 
      repeat light; t_closing.
      rewrite_open_none.
      apply_any; t_closer.
      remember H as H'; clear HeqH'.
      apply bs_closed_term in H; t_closing.
      apply bs_value in H'.
      repeat instantiate_cps_rec_pfv.
      instantiate_cps_rec_open_value.
      eapply ss_bs; [econstructor | idtac];
      eauto with open_value cps.
      repeat light.
      rewrite_open_none.
  - (* tright *)
    options; destruct_is_open_value; 
    repeat light || invert_constructor_equalities.
    + unshelve epose proof bs_unique t v t _ _; 
      try solve [
        t_closing; 
      t_closing;
        t_closing; 
        eauto using value_bs with values open_value
      ].
      repeat light || rewrite_any 
      || destruct_match || invert_constructor_equalities.
      eexists; repeat light; t_closing.
      eapply ss_bs; [econstructor | idtac]; 
      repeat light. 
      rewrite_open_none.
    + repeat light || invert_constructor_equalities 
      || destruct_match;
      unshelve epose proof H2 _ eq_refl; steps.
      eexists; repeat light.
      eapply ss_bs; [econstructor | idtac]; 
      repeat light; t_closing.
      rewrite_open_none.
      apply_any; t_closer.
      remember H as H'; clear HeqH'.
      apply bs_closed_term in H; t_closing.
      apply bs_value in H'.
      repeat instantiate_cps_rec_pfv.
      instantiate_cps_rec_open_value.
      eapply ss_bs; [econstructor | idtac];
      eauto with open_value cps.
      repeat light.
      rewrite_open_none.
  - (* sum_match (tleft _) _ _ *)
    unshelve epose proof cps_rec_defined_for_erased_wf_terms (open 0 tl (fvar 0 term_var)) 1 _ _.
    apply wf_open; t_closer.
    apply is_erased_open; t_closer.

    apply bs_closed_term in H; t_closer.
    apply bs_closed_term in H0; t_closer.
    unshelve epose proof cps_value_def_for_values v' _; t_closer.
    steps.
    eexists; repeat light; eauto with cps.
    eapply ss_bs.
    econstructor; t_closer.
    repeat light.
    rewrite_open_none; solve_wf_cps_rec.
    unshelve epose proof IHbcbv_step1 _ _ eq_refl; t_closer.
    steps.
    repeat light || options || destruct_match || invert_constructor_equalities.
    unshelve epose proof cps_rec_closed_value_is_value _ _ _ _ _ matched2;
    try solve [
      t_closing; 
      step_inversion cbv_value;
      eauto
    ].
    apply_any; try solve [
      t_closing;
      repeat instantiate_cps_rec_pfv;
      repeat instantiate_cps_rec_wf;
      eauto using fv_close_cps_rec, fv_close_nil2 with cps wf;
      solve_wf_cps_rec;
      solve_erased_terms_cps_rec
    ].
    eapply ss_bs.
    econstructor; t_closer.
    repeat light.
    rewrite_open_none; solve_wf_cps_rec.
    eapply BSmatchLeft.
    + constructor.
      apply value_bs.
      t_closer.
    + repeat light.
      rewrite open_close; solve_wf_cps_rec.
      rewrite_open_none; solve_wf_cps_rec.
      unshelve epose proof cps_subst _ _ 0 1 _ matched2 
        (open 0 tl (fvar 0 term_var)) false _ _;
      t_closer;
      repeat light || fv_open || list_utils || destruct_match;
      try solve [
        t_closing;
        step_inversion cbv_value;
        eauto
      ].
      repeat light || options || destruct_match || invert_constructor_equalities.
      rewrite substitute_open3 in *; t_closer.
      t_substitutions.
      rewrite (cps_rec_nf (open 0 tl v) 1 0 false) in *;
      repeat light || fv_open || list_utils || destruct_match; t_closer.
      unshelve epose proof IHbcbv_step2 _ _ H6; t_closer; steps.
      apply_any; t_closer.
      unfold cps_value in *.
      repeat light.
  - (* sum_match (tright _) _ _ *)
    unshelve epose proof cps_rec_defined_for_erased_wf_terms (open 0 tr (fvar 0 term_var)) 1 _ _.
    apply wf_open; t_closer.
    apply is_erased_open; t_closer.

    apply bs_closed_term in H; t_closer.
    apply bs_closed_term in H0; t_closer.
    unshelve epose proof cps_value_def_for_values v' _; t_closer.
    steps.
    eexists; repeat light; eauto with cps.
    eapply ss_bs.
    econstructor; t_closer.
    repeat light.
    rewrite_open_none; solve_wf_cps_rec.
    unshelve epose proof IHbcbv_step1 _ _ eq_refl; t_closer.
    steps.
    repeat light || options || destruct_match || invert_constructor_equalities.
    unshelve epose proof cps_rec_closed_value_is_value _ _ _ _ _ matched2;
    try solve [
      t_closing; 
      step_inversion cbv_value;
      eauto
    ].
    apply_any; try solve [
      t_closing;
      repeat instantiate_cps_rec_pfv;
      repeat instantiate_cps_rec_wf;
      eauto using fv_close_cps_rec, fv_close_nil2 with cps wf;
      solve_wf_cps_rec;
      solve_erased_terms_cps_rec
    ].
    eapply ss_bs.
    econstructor; t_closer.
    repeat light.
    rewrite_open_none; solve_wf_cps_rec.
    eapply BSmatchRight.
    + constructor.
      apply value_bs.
      t_closer.
    + repeat light.
      rewrite open_close; solve_wf_cps_rec.
      rewrite_open_none; solve_wf_cps_rec.
      unshelve epose proof cps_subst _ _ 0 1 _ matched2 
        (open 0 tr (fvar 0 term_var)) false _ _;
      t_closer;
      repeat light || fv_open || list_utils || destruct_match;
      try solve [
        t_closing;
        step_inversion cbv_value;
        eauto
      ].
      repeat light || options || destruct_match || invert_constructor_equalities.
      rewrite substitute_open3 in *; t_closer.
      t_substitutions.
      rewrite (cps_rec_nf (open 0 tr v) 1 0 false) in *;
      repeat light || fv_open || list_utils || destruct_match; t_closer.
      unshelve epose proof IHbcbv_step2 _ _ H6; t_closer; steps.
      apply_any; t_closer.
      unfold cps_value in *.
      repeat light.
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
  - econstructor.
  - eapply value_bs; eauto.
    apply bs_closed_term in H; light.
    eapply cps_rec_closed_value_is_value in H; eauto.
    t_closer.
  - light.
    apply value_bs.
    eapply (cps_rec_closed_value_is_value v); eauto with values.
Qed.
