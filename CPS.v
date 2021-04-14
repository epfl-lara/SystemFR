Require Import SystemFR.Trees.
Require Import SystemFR.SmallStep.
Require Import SystemFR.Syntax.
Require Import SystemFR.Evaluator.

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
          close 1 csp_open_t nf
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

Eval compute in (cps_rec (succ zero) 0).

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
    let close_t : option tree := option_map (fun cps_t => close 1 cps_t 0) cps_t in
      option_map (fun close_t => notype_lambda (close_t)) close_t
  | _ => None
  end.

Hint Unfold cps_value : cps.

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

(* Lemma cps_of_value_is_value_for_lambda: forall t t', 
  closed_term (notype_lambda t) -> cps_value (notype_lambda t) = Some (notype_lambda).
Proof.
  
Qed.


Lemma cps_of_value_is_value: forall v cps_v,
  closed_value v -> cps_value v = Some cps_v -> closed_value cps_v.
Proof.
  intros v cps_v [Hvclosed Hvvalue] H.
  induction Hvvalue; simpl in H; split;
  try solve [inversion H; repeat assumption || constructor];
  destruct (cps_rec (open 0 t (fvar 0 term_var)) 1) eqn:E; inversion H;
  try solve [constructor].
  repeat split; simpl.
Admitted. *)

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

Lemma cps_rec_outputs_erased_terms: forall t nf cps_t,
  cps_rec t nf = Some cps_t -> is_erased_term cps_t.
Proof.
  induction t; light; simp cps_rec in H;
  repeat destruct_match; inversion H; simpl; step.
  
Admitted.


Lemma cps_rec_keeps_closed_terms_closed: forall size_t t nf fvs cps_t, 
  tree_size t <= size_t ->
    wf t nf -> is_erased_term t -> pfv t term_var = fvs -> 
      cps_rec t nf = Some cps_t -> 
        wf cps_t nf /\ is_erased_term cps_t /\ pfv cps_t term_var = fvs.
Proof.
  induction size_t; light;
  destruct t; try solve [inversion H;
  repeat destruct_match || simp cps_rec in H3 || simpl in *;
  repeat t_equality || step || simpl || lia];
  simpl in H.

  simp cps_rec in H3.
  destruct_match;
  inversion H3; 
  clear H3.
  simpl in *.
  step.
  lia.
  apply (open_keeps_wf _ 0 _ nf) in H0.
  apply le_S_n in H.
  apply (open_keeps_is_erased _ 0 nf) in H1.
  rewrite <- (open_t_size _ 0 nf) in H.
  eapply (IHsize_t (open 0 t (fvar nf term_var)) (S nf) _ t0) in H as [H [H' H'']]; 
  try assumption.
  apply wf_S, (close_keeps_wf _ nf 1 _) in H. assumption.
  lia.
  auto.
  apply close_keeps_is_erased.
  apply cps_rec_outputs_erased_terms in matched. assumption.
  

  


  (* destruct t; repeat destruct_match || simpl in *.


  intro t; induction (tree_size t) eqn:E;
  try solve [light; destruct t; 
  repeat destruct_match || simp cps_rec in H2 || simpl in *;
  repeat t_equality || step || simpl || lia].
  

  induction t; light; simpl in *;
  repeat destruct_match || simp cps_rec in H2; inversion H2; step; simpl; step;
  try solve [auto; step; try lia; rewrite matched; auto].
  eapply IHt in H.
  step. *)
Admitted.

Lemma cps_keeps_closed_terms_closed: forall t cps_t, 
  closed_term t -> cps t = Some cps_t -> closed_term cps_t.
Proof.
  intros t cps_t [Hfvs [Hwf Herased]] Hcps.
  eapply cps_rec_keeps_closed_terms_closed in Hwf as [Hcpswf [Hcpserased Hcpsfvs]]; eauto.
  repeat split; assumption.
Qed.

Lemma cps_rec_correct: 
  forall p var cps_p nf,
    wf p var ->
      is_erased_term p ->
        cps_rec p nf = Some cps_p -> 
          exists v, p ~>* v /\ cps_value v = Some cps_v ->
          (app cps_p (notype_lambda (lvar 0 term_var))) ~>* cps_v.
Proof.
  
Admitted.

Theorem cps_correct: 
  forall p cps_p v,  closed_value v ->
    closed_term p -> p ~>* v ->
      cps p = Some cps_p -> exists cps_v, cps_value v = Some cps_v /\
        (app cps_p (notype_lambda (lvar 0 term_var))) ~>* cps_v.
Proof.
  (* light. generalize dependent v.  
  induction p; light; destruct H as [Hvclosed Hvvalue]; destruct H0 as [Hfv [Hwf Herased]];
  try destruct Herased; try inversion H2.
  - (* p = fvar n f *)
    destruct f; steps; try inversion Hfv.
  - (* p = uu *) 
    inversion H1; light; inversion H3; light.
    constructor 2 with (y := (app (notype_lambda (lvar 0 term_var)) uu)); repeat constructor.
    constructor 2 with (y := uu); try constructor; auto.
    assert (A : cbv_value uu). constructor.
    apply evaluate_step2 with (t := y) in A; auto.
    contradiction.
  - (* p = notype_lambda p *)
Qed. *)
Admitted.

End CPS.
