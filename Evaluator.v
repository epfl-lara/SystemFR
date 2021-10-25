Require Export SystemFR.TypeErasure.
Require Export SystemFR.Freshness.
Require Export SystemFR.Notations.

Require Export SystemFR.SmallStep.

Require Import Coq.Strings.String.
Open Scope bool_scope.

(* Helpers *)

Fixpoint is_nat (t : tree) : bool :=
  match t with
    | zero => true
    | succ t1 => is_nat t1
    | _ => false
end.

Fixpoint is_open_value (t: tree) : bool :=
  match t with
    | fvar _ term_var => true
    | uu => true
    | ttrue => true
    | tfalse => true
    | pp e1 e2 => andb (is_open_value e1) (is_open_value e2)
    | tleft e1 => (is_open_value e1)
    | tright e1 => (is_open_value e1)
    | zero => true
    | succ e1 => (is_open_value e1)
    | notype_lambda _ => true
    | _ => false end.

Ltac destruct_is_open_value := 
  match goal with
  | [ |- context[is_open_value ?t]] => 
    let is_open_value_eqn := fresh "is_open_value_eqn" in
    destruct (is_open_value t) eqn:is_open_value_eqn
  | [H: context[is_open_value ?t] |- _] => 
    let is_open_value_eqn := fresh "is_open_value_eqn" in
    destruct (is_open_value t) eqn:is_open_value_eqn
  end.

Lemma no_free_var_open_value_is_value : forall v, 
  is_open_value v = true ->
  pfv v term_var = nil -> 
    cbv_value v.
Proof.
  induction v;
  repeat light || destruct_match || list_utils || bools; 
  try discriminate;
  eauto with values.
Qed.

#[export] Hint Resolve no_free_var_open_value_is_value : open_value.

Lemma cbv_value_is_open_value_true: forall v,
  cbv_value v -> is_open_value v = true.
Proof.
  induction 1; repeat light || bools.
Qed.

#[export] Hint Resolve cbv_value_is_open_value_true : open_value.

Lemma cbv_value_is_open_value_false_contra: forall v,
  cbv_value v -> 
  is_open_value v = false -> 
    False.
Proof.
  induction 1; repeat light || bools.
Qed.

#[export] Hint Immediate cbv_value_is_open_value_false_contra : open_value.

Fixpoint is_value (t: tree) : bool :=
  match t with
    | uu => true
    | ttrue => true
    | tfalse => true
    | pp e1 e2 => andb (is_value e1) (is_value e2)
    | tleft e1 => (is_value e1)
    | tright e1 => (is_value e1)
    | zero => true
    | succ e1 => (is_value e1)
    | notype_lambda _ => true
    | _ => false end.

Lemma is_value_correct : forall v, is_value v = true <-> cbv_value v.
Proof.
  split.
  - induction v; repeat step || bools; eauto with values.
  - induction 1; repeat step || bools.
Defined.


Definition get_pair t : {t': option (tree*tree) | forall t1 t2, t' = Some (t1, t2) <-> t = pp t1 t2}.
Proof.
  exists ( match t with
      | pp e1 e2 => Some (e1,e2)
      | _ => None end).
  destruct t; steps.
Defined.

Definition get_app t : {t': option tree | forall t1, t' = Some t1 <-> t = notype_lambda t1}.
Proof.
  exists (match t with
     | notype_lambda body => Some body
     | _ => None end).
  destruct t; steps.
Defined.

Definition get_LR t : {t': option tree | forall t1, t' = Some t1 <-> (t = tleft t1 \/ t = tright t1)}.
Proof.
  exists (match t with
     | tleft t' => Some t'
     | tright t' => Some t'
     | _ => None end).
  destruct t; steps.
Defined.

Fixpoint get_nat t :=
  match t with
  | zero => Some 0
  | succ t => option_map S (get_nat t)
  | _ => None
  end.

Lemma get_nat_build_nat :
  forall n, get_nat (build_nat n) = Some n.
Proof.
  induction n; repeat steps || rewrite_any.
Qed.

Lemma get_nat_prop :
  forall t n, get_nat t = Some n -> t = build_nat n.
Proof.
  induction t; steps.
  destruct n; unfold option_map in *; steps.
Qed.


Definition ss_eval_binary_primitive (o:op) t1 t2 :=
  match (get_nat t1), (get_nat t2) with
  | (Some n1), (Some n2) => (
      match o with
      | Eq => Some (if (PeanoNat.Nat.eqb n1 n2) then ttrue else tfalse)
      | Neq => Some (if (PeanoNat.Nat.eqb n1 n2) then tfalse else ttrue)
      | Plus => Some (build_nat (n1 + n2))
      | Minus => if (PeanoNat.Nat.leb n2 n1) then
                  Some (build_nat (Nat.sub n1 n2))
                else None
      | Mul => Some (build_nat (n1 * n2))
      | Div => if (PeanoNat.Nat.ltb 0 n2) then
                Some (build_nat (PeanoNat.Nat.div n1 n2))
              else None
      | Lt => Some (if (PeanoNat.Nat.ltb n1 n2) then ttrue else tfalse)
      | Leq => Some (if (PeanoNat.Nat.leb n1 n2) then ttrue else tfalse)
      | Gt => Some (if (PeanoNat.Nat.leb n1 n2) then tfalse else ttrue)
      | Geq => Some (if (PeanoNat.Nat.ltb n1 n2) then tfalse else ttrue)
      | And | Or | Not | Cup | Nop => None  end)
  | _, _ => match o,t1,t2 with
           | And, ttrue, ttrue => Some ttrue
           | And, ttrue, tfalse => Some tfalse
           | And, tfalse, ttrue => Some tfalse
           | And, tfalse, tfalse => Some tfalse
           | Or, ttrue, ttrue => Some ttrue
           | Or, ttrue, tfalse => Some ttrue
           | Or, tfalse, ttrue => Some ttrue
           | Or, tfalse, tfalse => Some tfalse
           | _,_,_ => None end
  end.

Opaque PeanoNat.Nat.leb.
Opaque PeanoNat.Nat.ltb.

Ltac natb_rewrites :=
  repeat rewrite PeanoNat.Nat.leb_le in * || rewrite PeanoNat.Nat.ltb_lt in * || rewrite PeanoNat.Nat.eqb_eq in * || rewrite PeanoNat.Nat.eqb_neq in * || rewrite PeanoNat.Nat.ltb_nlt in * || rewrite PeanoNat.Nat.leb_nle in *.

Lemma ss_eval_binary_primitive_prop :
  forall o t1 t2 t,
    cbv_value t1 ->
    cbv_value t2 ->
    ss_eval_binary_primitive o t1 t2 = Some t <-> scbv_step (binary_primitive o t1 t2) t.
Proof.
  split; intros.
  + unfold ss_eval_binary_primitive in *; steps;
      repeat apply_anywhere get_nat_prop ; subst ;
        eapply scbv_step_same; try constructor ; repeat steps || natb_rewrites.
  + t_invert_step; steps.
    all: try solve [
               unfold ss_eval_binary_primitive;
               repeat rewrite get_nat_build_nat in * || natb_rewrites || steps] .
    all: try solve [
               exfalso;
               eauto using evaluate_step ].
Qed.

Lemma ss_eval_binary_primitive_prop2 :
  forall o t1 t2 t,
    is_value t1 = true ->
    is_value t2 = true ->
    ss_eval_binary_primitive o t1 t2 = Some t <-> scbv_step (binary_primitive o t1 t2) t.
Proof.
  intros. repeat rewrite is_value_correct in *. eauto using ss_eval_binary_primitive_prop.
Qed.


(* Evaluator (smallstep) *)
Fixpoint ss_eval (t: tree) {struct t}: (option tree) :=
  match t with
  | ite ttrue t1 t2 => Some t1
  | ite tfalse t1 t2 => Some t2
  | ite t t1 t2 => option_map (fun e => ite e t1 t2) (ss_eval t)

  | pp e1 e2 => match (is_value e1) with
               | true => option_map (pp e1) (ss_eval e2)
               | false => option_map (fun e => pp e e2) (ss_eval e1) end

  | pi1 t => match get_pair t with
            | exist _ None _  => option_map pi1 (ss_eval t)
            | exist _ (Some (e1, e2)) _ =>
              if (is_value e1) && (is_value e2)
              then Some e1
              else option_map pi1 (ss_eval t) end

  | pi2 t => match get_pair t with
            | exist _ None _ => option_map pi2 (ss_eval t)
            | exist _ (Some (e1, e2)) _ =>
              if (is_value e1) && (is_value e2)
              then Some e2
              else option_map pi2 (ss_eval t) end

  | app t1 t2 => match (is_value t1) with
                | true => match get_app t1 with
                         | exist _ None _ => option_map (app t1) (ss_eval t2)
                         | exist _ (Some ts) _ =>
                           if (is_value t2)
                           then Some (open 0 ts t2)
                           else option_map (app t1) (ss_eval t2) end
                | false => option_map (fun e => app e t2) (ss_eval t1) end

  | notype_tfix ts => Some (open 0 (open 1 ts zero) (notype_tfix ts))

  | succ t => option_map succ (ss_eval t)

  | tmatch t1 t0 ts => match t1 with
                      | zero => Some t0
                      | succ t2 =>
                        if (is_value t2)
                        then Some (open 0 ts t2)
                        else option_map (fun e => tmatch e t0 ts) (ss_eval t1)
                      | _ => option_map (fun e => tmatch e t0 ts) (ss_eval t1) end

  | sum_match t tl tr => if (is_value t) then match t with
                                             | tleft v => Some (open 0 tl v)
                                             | tright v => Some (open 0 tr v)
                                             | _ => None end
                        else option_map (fun e => sum_match e tl tr) (ss_eval t)

  | tleft t => option_map tleft (ss_eval t)
  | tright t => option_map tright (ss_eval t)

  | tsize t => if (is_value t) then Some (build_nat (tsize_semantics t)) else (option_map tsize (ss_eval t))
  | boolean_recognizer r t => if (is_value t) then match r with
                                                  | 0 => Some (is_pair t)
                                                  | 1 => Some (is_succ t)
                                                  | 2 => Some (is_lambda t)
                                                  | _ => None end
                             else option_map (boolean_recognizer r) (ss_eval t)

  | unary_primitive o t => match (is_value t) with
                          | false => option_map (unary_primitive o) (ss_eval t)
                          | true => match o with
                                   | Not => match t with
                                           | ttrue => Some (tfalse)
                                           | tfalse => Some (ttrue)
                                           | _ => None end
                                   | _ => None end
                          end

  | binary_primitive o t1 t2 => match (is_value t1) with
                               | false => option_map (fun e => binary_primitive o e t2) (ss_eval t1)
                               | true => match (is_value t2) with
                                        | false => option_map (binary_primitive o t1) (ss_eval t2)
                                        | true => ss_eval_binary_primitive o t1 t2 end
                               end

  | _ => None
  end.

(* Compute a certain number of small steps *)
Fixpoint ss_eval_n (t : tree) (k: nat) : (option tree) :=
  match k with
  | 0 => Some t
  | S k' => match ss_eval t with
           | Some t' => ss_eval_n t' k'
           | None => Some t end
  end.

(* Entry point for evaluation *)
Definition eval (t: tree) (k: nat): (option tree) :=
  ss_eval_n (erase_term t) k.


(* Tactics *)
Ltac destruct_sig :=
  match goal with
  | H: _ |- context[let _ := get_pair ?t in _ ]  =>
    let fresh := fresh "get_pair" in destruct (get_pair t) (* eqn:fresh *)
  | H: context[get_pair ?t = _ ] |- _ =>
    let fresh := fresh "get_pair" in destruct (get_pair t) (* eqn:fresh *)
  | H: context[_ = get_pair ?t ] |- _ =>
    let fresh := fresh "get_pair" in destruct (get_pair t) (* eqn:fresh *)
  | H: context[get_app ?t = _ ] |- _ =>
    let fresh := fresh "get_app" in destruct (get_app t) (* eqn:fresh *)
  | H: context[_ = get_app ?t ] |- _ =>
    let fresh := fresh "get_app" in destruct (get_app t) (* eqn:fresh *)
  end. (* match on type of t = sig *)

Ltac destruct_ss_eval :=
  match goal with
  | H: context[ss_eval ?t] |- _ => destruct (ss_eval t) end.


(* Results *)
Lemma ss_eval_step : forall t t', ss_eval t = Some t' -> is_value t = true -> False.
Proof.
  induction t; repeat step || options.
Qed.

Ltac ss_eval_step :=
  match goal with
  |H: ss_eval ?t1 = Some ?t2 |- _ => poseNew (Mark (t1, t2) "ss_eval_step_h");
                                   pose proof  (ss_eval_step _ _ H) end.

Lemma is_value_build_nat_false:
  forall n,
    is_value (build_nat n) = false -> False.
Proof.
  intros.
  assert (is_value (build_nat n) = true ). rewrite is_value_correct; eauto with values.
  steps.
Qed.

Ltac is_value_build_nat_false :=
  match goal with
  |H: is_value (build_nat ?n) = false |- _ => exfalso; apply (is_value_build_nat_false n H)
  end.

Lemma ss_eval_correct2: forall t t',
    pfv t term_var = nil ->
    t ~> t' ->
    ss_eval t = Some t'.
Proof.
  intros.
  induction H0 ;
    repeat light || options || invert_constructor_equalities
    || ss_eval_step || destruct_sig || instantiate_eq_refl
    || list_utils || bools
    || (rewrite <- is_value_correct in * )
    || (rewrite get_nat_build_nat in * )
    || natb_rewrites
    || is_value_build_nat_false
    || (eauto using ss_eval_binary_primitive_prop2, fv_nil_top_level_var with smallstep values)
    || destruct_match || unfold ss_eval_binary_primitive.
Qed.

Lemma ss_eval_correct1: forall t t',
    ss_eval t = Some t' ->
    pfv t term_var = nil ->
    t ~> t'.
Proof.
  induction t;
    intros ;
    repeat light ; destruct_ss_eval ;
      repeat light || options || bools
      || list_utils || instantiate_eq_refl || invert_constructor_equalities
      || (rewrite is_value_correct in *)
         || destruct_sig || congruence
         ||  step_inversion cbv_value || destruct_match ;
         eauto using ss_eval_binary_primitive_prop2, ss_eval_step with smallstep values.
         all: try solve [
                    apply ss_eval_binary_primitive_prop; eauto ].
Qed.

(* Main theorem : the evaluator corresponds to the small call-by-value steps *)
Theorem ss_eval_correct : forall t t',
    pfv t term_var = nil ->
    ss_eval t = Some t' <-> t ~> t'.
Proof.
  split; eauto using ss_eval_correct1, ss_eval_correct2.
Qed.

(* Extraction *)
(*
Require Extraction.

Extraction Language Ocaml.
Set Extraction AccessOpaque.

Extraction "evaluator.ml" eval.
 *)
