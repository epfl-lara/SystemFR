
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module Nat =
 struct
  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S m0 -> eq_dec n0 m0)
 end

type fv_tag =
| Term_var
| Type_var

type tree =
| Fvar of nat * fv_tag
| Lvar of nat * fv_tag
| T_nat
| T_unit
| T_bool
| T_arrow of tree * tree
| T_prod of tree * tree
| T_sum of tree * tree
| T_refine of tree * tree
| T_type_refine of tree * tree
| T_intersection of tree * tree
| T_union of tree * tree
| T_top
| T_bot
| T_equiv of tree * tree
| T_forall of tree * tree
| T_exists of tree * tree
| T_abs of tree
| T_rec of tree * tree * tree
| Err of tree
| Notype_err
| Uu
| Tsize of tree
| Lambda of tree * tree
| Notype_lambda of tree
| App of tree * tree
| Forall_inst of tree * tree
| Pp of tree * tree
| Pi1 of tree
| Pi2 of tree
| Because of tree * tree
| Get_refinement_witness of tree * tree
| Ttrue
| Tfalse
| Ite of tree * tree * tree
| Boolean_recognizer of nat * tree
| Zero
| Succ of tree
| Tmatch of tree * tree * tree
| Tfix of tree * tree
| Notype_tfix of tree
| Tlet of tree * tree * tree
| Notype_tlet of tree * tree
| Type_abs of tree
| Type_inst of tree * tree
| Tfold of tree * tree
| Tunfold of tree
| Tunfold_in of tree * tree
| Tunfold_pos_in of tree * tree
| Tright of tree
| Tleft of tree
| Sum_match of tree * tree * tree
| Typecheck of tree * tree
| Trefl of tree * tree

(** val build_nat : nat -> tree **)

let rec build_nat = function
| O -> Zero
| S n0 -> Succ (build_nat n0)

(** val open0 : nat -> tree -> tree -> tree **)

let rec open0 k t rep =
  match t with
  | Lvar (i, f) -> (match f with
                    | Term_var -> (match Nat.eq_dec k i with
                                   | Left -> rep
                                   | Right -> t)
                    | Type_var -> t)
  | T_arrow (t1, t2) -> T_arrow ((open0 k t1 rep), (open0 (S k) t2 rep))
  | T_prod (t1, t2) -> T_prod ((open0 k t1 rep), (open0 (S k) t2 rep))
  | T_sum (t1, t2) -> T_sum ((open0 k t1 rep), (open0 k t2 rep))
  | T_refine (t0, p) -> T_refine ((open0 k t0 rep), (open0 (S k) p rep))
  | T_type_refine (t1, t2) -> T_type_refine ((open0 k t1 rep), (open0 (S k) t2 rep))
  | T_intersection (t1, t2) -> T_intersection ((open0 k t1 rep), (open0 k t2 rep))
  | T_union (t1, t2) -> T_union ((open0 k t1 rep), (open0 k t2 rep))
  | T_equiv (t1, t2) -> T_equiv ((open0 k t1 rep), (open0 k t2 rep))
  | T_forall (t1, t2) -> T_forall ((open0 k t1 rep), (open0 (S k) t2 rep))
  | T_exists (t1, t2) -> T_exists ((open0 k t1 rep), (open0 (S k) t2 rep))
  | T_abs t0 -> T_abs (open0 k t0 rep)
  | T_rec (n, t0, ts) -> T_rec ((open0 k n rep), (open0 k t0 rep), (open0 k ts rep))
  | Err t0 -> Err (open0 k t0 rep)
  | Tsize t0 -> Tsize (open0 k t0 rep)
  | Lambda (t0, t') -> Lambda ((open0 k t0 rep), (open0 (S k) t' rep))
  | Notype_lambda t' -> Notype_lambda (open0 (S k) t' rep)
  | App (t1, t2) -> App ((open0 k t1 rep), (open0 k t2 rep))
  | Forall_inst (t1, t2) -> Forall_inst ((open0 k t1 rep), (open0 k t2 rep))
  | Pp (t1, t2) -> Pp ((open0 k t1 rep), (open0 k t2 rep))
  | Pi1 t0 -> Pi1 (open0 k t0 rep)
  | Pi2 t0 -> Pi2 (open0 k t0 rep)
  | Because (t1, t2) -> Because ((open0 k t1 rep), (open0 k t2 rep))
  | Get_refinement_witness (t1, t2) -> Get_refinement_witness ((open0 k t1 rep), (open0 (S k) t2 rep))
  | Ite (t1, t2, t3) -> Ite ((open0 k t1 rep), (open0 k t2 rep), (open0 k t3 rep))
  | Boolean_recognizer (r, t0) -> Boolean_recognizer (r, (open0 k t0 rep))
  | Succ t' -> Succ (open0 k t' rep)
  | Tmatch (t', t1, t2) -> Tmatch ((open0 k t' rep), (open0 k t1 rep), (open0 (S k) t2 rep))
  | Tfix (t0, t') -> Tfix ((open0 (S k) t0 rep), (open0 (S (S k)) t' rep))
  | Notype_tfix t' -> Notype_tfix (open0 (S (S k)) t' rep)
  | Tlet (t1, t0, t2) -> Tlet ((open0 k t1 rep), (open0 k t0 rep), (open0 (S k) t2 rep))
  | Notype_tlet (t1, t2) -> Notype_tlet ((open0 k t1 rep), (open0 (S k) t2 rep))
  | Type_abs t0 -> Type_abs (open0 k t0 rep)
  | Type_inst (t0, t1) -> Type_inst ((open0 k t0 rep), (open0 k t1 rep))
  | Tfold (t0, t') -> Tfold ((open0 k t0 rep), (open0 k t' rep))
  | Tunfold t' -> Tunfold (open0 k t' rep)
  | Tunfold_in (t1, t2) -> Tunfold_in ((open0 k t1 rep), (open0 (S k) t2 rep))
  | Tunfold_pos_in (t1, t2) -> Tunfold_pos_in ((open0 k t1 rep), (open0 (S k) t2 rep))
  | Tright t' -> Tright (open0 k t' rep)
  | Tleft t' -> Tleft (open0 k t' rep)
  | Sum_match (t', tl, tr) -> Sum_match ((open0 k t' rep), (open0 (S k) tl rep), (open0 (S k) tr rep))
  | Typecheck (t0, t1) -> Typecheck ((open0 k t0 rep), (open0 k t1 rep))
  | Trefl (t1, t2) -> Trefl ((open0 k t1 rep), (open0 k t2 rep))
  | _ -> t

(** val erase_term : tree -> tree **)

let rec erase_term t = match t with
| Fvar (_, f) -> (match f with
                  | Term_var -> t
                  | Type_var -> Uu)
| Lvar (_, f) -> (match f with
                  | Term_var -> t
                  | Type_var -> Uu)
| Err _ -> Notype_err
| Tsize t0 -> Tsize (erase_term t0)
| Lambda (_, t') -> Notype_lambda (erase_term t')
| Notype_lambda t0 -> Notype_lambda (erase_term t0)
| App (t1, t2) -> App ((erase_term t1), (erase_term t2))
| Forall_inst (t1, _) -> erase_term t1
| Pp (t1, t2) -> Pp ((erase_term t1), (erase_term t2))
| Pi1 t' -> Pi1 (erase_term t')
| Pi2 t' -> Pi2 (erase_term t')
| Because (t1, _) -> erase_term t1
| Get_refinement_witness (_, t2) -> App ((Notype_lambda (erase_term t2)), Uu)
| Ttrue -> Ttrue
| Tfalse -> Tfalse
| Ite (t1, t2, t3) -> Ite ((erase_term t1), (erase_term t2), (erase_term t3))
| Boolean_recognizer (r, t0) -> Boolean_recognizer (r, (erase_term t0))
| Zero -> Zero
| Succ t' -> Succ (erase_term t')
| Tmatch (t', t0, ts) -> Tmatch ((erase_term t'), (erase_term t0), (erase_term ts))
| Tfix (_, t0) -> Notype_tfix (erase_term t0)
| Notype_tfix t0 -> Notype_tfix (erase_term t0)
| Tlet (t1, _, t2) -> App ((Notype_lambda (erase_term t2)), (erase_term t1))
| Notype_tlet (t1, t2) -> App ((Notype_lambda (erase_term t2)), (erase_term t1))
| Type_abs t0 -> erase_term t0
| Type_inst (t0, _) -> erase_term t0
| Tfold (_, t') -> erase_term t'
| Tunfold t' -> erase_term t'
| Tunfold_in (t1, t2) -> App ((Notype_lambda (erase_term t2)), (erase_term t1))
| Tunfold_pos_in (t1, t2) -> App ((Notype_lambda (erase_term t2)), (erase_term t1))
| Tright t' -> Tright (erase_term t')
| Tleft t' -> Tleft (erase_term t')
| Sum_match (t', tl, tr) -> Sum_match ((erase_term t'), (erase_term tl), (erase_term tr))
| Typecheck (t0, _) -> erase_term t0
| _ -> Uu

(** val tsize_semantics : tree -> nat **)

let rec tsize_semantics = function
| Pp (t1, t2) -> add (add (S O) (tsize_semantics t1)) (tsize_semantics t2)
| Succ t' -> add (S O) (tsize_semantics t')
| Tright t0 -> add (S O) (tsize_semantics t0)
| Tleft t0 -> add (S O) (tsize_semantics t0)
| _ -> O

(** val is_pair : tree -> tree **)

let is_pair = function
| Pp (_, _) -> Ttrue
| _ -> Tfalse

(** val is_succ : tree -> tree **)

let is_succ = function
| Succ _ -> Ttrue
| _ -> Tfalse

(** val is_lambda : tree -> tree **)

let is_lambda = function
| Notype_lambda _ -> Ttrue
| _ -> Tfalse

(** val isValue : tree -> bool **)

let rec isValue = function
| Uu -> True
| Notype_lambda _ -> True
| Pp (e1, e2) -> (match isValue e1 with
                  | True -> isValue e2
                  | False -> False)
| Ttrue -> True
| Tfalse -> True
| Zero -> True
| Succ e1 -> isValue e1
| Tright e1 -> isValue e1
| Tleft e1 -> isValue e1
| _ -> False

(** val getPair : tree -> (tree, tree) prod option **)

let getPair = function
| Pp (e1, e2) -> Some (Pair (e1, e2))
| _ -> None

(** val getApp : tree -> tree option **)

let getApp = function
| Notype_lambda body -> Some body
| _ -> None

(** val ss_eval : tree -> tree option **)

let rec ss_eval = function
| Tsize t0 ->
  (match isValue t0 with
   | True -> Some (build_nat (tsize_semantics t0))
   | False -> option_map (fun x -> Tsize x) (ss_eval t0))
| App (t1, t2) ->
  (match isValue t1 with
   | True ->
     (match getApp t1 with
      | Some ts ->
        (match isValue t2 with
         | True -> Some (open0 O ts t2)
         | False -> option_map (fun x -> App (t1, x)) (ss_eval t2))
      | None -> option_map (fun x -> App (t1, x)) (ss_eval t2))
   | False -> option_map (fun e -> App (e, t2)) (ss_eval t1))
| Pp (e1, e2) ->
  (match isValue e1 with
   | True -> option_map (fun x -> Pp (e1, x)) (ss_eval e2)
   | False -> option_map (fun e -> Pp (e, e2)) (ss_eval e1))
| Pi1 t0 ->
  (match getPair t0 with
   | Some p ->
     let Pair (e1, e2) = p in
     (match match isValue e1 with
            | True -> isValue e2
            | False -> False with
      | True -> Some e1
      | False -> option_map (fun x -> Pi1 x) (ss_eval t0))
   | None -> option_map (fun x -> Pi1 x) (ss_eval t0))
| Pi2 t0 ->
  (match getPair t0 with
   | Some p ->
     let Pair (e1, e2) = p in
     (match match isValue e1 with
            | True -> isValue e2
            | False -> False with
      | True -> Some e2
      | False -> option_map (fun x -> Pi2 x) (ss_eval t0))
   | None -> option_map (fun x -> Pi2 x) (ss_eval t0))
| Ite (t0, t1, t2) ->
  (match t0 with
   | Ttrue -> Some t1
   | Tfalse -> Some t2
   | _ -> option_map (fun e -> Ite (e, t1, t2)) (ss_eval t0))
| Boolean_recognizer (r, t0) ->
  (match isValue t0 with
   | True ->
     (match r with
      | O -> Some (is_pair t0)
      | S n ->
        (match n with
         | O -> Some (is_succ t0)
         | S n0 -> (match n0 with
                    | O -> Some (is_lambda t0)
                    | S _ -> None)))
   | False -> option_map (fun x -> Boolean_recognizer (r, x)) (ss_eval t0))
| Succ t0 -> option_map (fun x -> Succ x) (ss_eval t0)
| Tmatch (t1, t0, ts) ->
  (match t1 with
   | Zero -> Some t0
   | Succ t2 ->
     (match isValue t2 with
      | True -> Some (open0 O ts t2)
      | False -> option_map (fun e -> Tmatch (e, t0, ts)) (ss_eval t1))
   | _ -> option_map (fun e -> Tmatch (e, t0, ts)) (ss_eval t1))
| Notype_tfix ts -> Some (open0 O (open0 (S O) ts Zero) (Notype_tfix ts))
| Tright t0 -> option_map (fun x -> Tright x) (ss_eval t0)
| Tleft t0 -> option_map (fun x -> Tleft x) (ss_eval t0)
| Sum_match (t0, tl, tr) ->
  (match isValue t0 with
   | True -> (match t0 with
              | Tright v -> Some (open0 O tr v)
              | Tleft v -> Some (open0 O tl v)
              | _ -> None)
   | False -> option_map (fun e -> Sum_match (e, tl, tr)) (ss_eval t0))
| _ -> None

(** val ss_eval_n : tree -> nat -> tree option **)

let rec ss_eval_n t = function
| O -> Some t
| S k' -> (match ss_eval t with
           | Some t' -> ss_eval_n t' k'
           | None -> Some t)

(** val eval : tree -> nat -> tree option **)

let eval t k =
  ss_eval_n (erase_term t) k

(** val capturedVariable2_example : tree **)

let capturedVariable2_example =
  Notype_tlet ((Notype_tfix (Notype_lambda (Notype_lambda (Tmatch ((Lvar (O, Term_var)), (Lvar ((S O), Term_var)),
    (Tmatch ((Lvar ((S (S O)), Term_var)), Zero, (App ((App ((Lvar ((S (S (S (S O)))), Term_var)), (Lvar (O,
    Term_var)))), (Lvar ((S O), Term_var))))))))))), (Notype_tlet ((Notype_tfix (Notype_lambda (Tmatch ((Lvar (O,
    Term_var)), Zero, (Succ (Succ (App ((Lvar ((S (S O)), Term_var)), (Lvar (O, Term_var)))))))))), (Notype_tlet
    ((Notype_tlet ((Succ (Succ (Succ (Succ (Succ Zero))))), (Notype_tlet ((Notype_lambda (App ((Lvar ((S (S O)),
    Term_var)), (Lvar (O, Term_var))))), (Notype_tlet ((App ((Lvar (O, Term_var)), (Lvar ((S O), Term_var)))),
    (App ((App ((Lvar ((S (S (S (S O)))), Term_var)), (Lvar (O, Term_var)))), (Lvar (O, Term_var)))))))))), (Lvar
    (O, Term_var)))))))
