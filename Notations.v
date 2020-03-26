Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Freshness.


Open Scope list.

Declare Custom Entry expr.
Declare Custom Entry type.

(* Entry point *)
Notation "[| x |]" := x (x custom expr at level 2).
Notation "( x )" := x (in custom expr, x custom expr).
Notation "|[ x ]|" := x (in custom expr, x constr).
Notation "x" := x (in custom expr at level 0, x ident).

(* Variables (nameless) *)
Notation "'ft{' v '}'" := (fvar v term_var) (in custom expr,
                                                v constr).
Notation "'fT{' t '}'" := (fvar t type_var) (in custom type,
                                                t constr).
Notation "'lt{' v '}'" := (lvar v term_var) (in custom expr,
                                                v constr).
Notation "'lT{' t '}'" := (lvar t type_var) (in custom type at level 4,
                                                t constr at level 4).
(* Untyped language *)
(* --------------------------------------------------------------------- *)

Notation "'()'" := (uu) (in custom expr).

Notation "'size' ( t )" := (tsize t) (in custom expr at level 1,
                                         t custom expr at level 4).


Notation "'fun' => y" := (notype_lambda y) (in custom expr at level 4,
                                              y custom expr at level 4).
Notation "'def' f : y" := (notype_lambda y) (in custom expr at level 100,
                                                f ident,
                                                y custom expr at level 4).
Notation " t1 t2 " := (app t1 t2) (in custom expr at level 2,
                                      t1 custom expr,
                                      t2 custom expr at level 4).
(* Pairs *)

Notation "( t1 , t2 , .. , tn )" := (pp .. (pp t1 t2) .. tn) (in custom expr,
                                           t1 custom expr,
                                           t2 custom expr,
                                           tn custom expr).
Notation "t '._1'" := (pi1 t) (in custom expr at level 2,
                                  t custom expr).
Notation "t '._2'" := (pi2 t) (in custom expr at level 2,
                                  t custom expr).

(* Booleans *)
Notation "'true'" := (ttrue) (in custom expr).
Notation "'false'" := (tfalse) (in custom expr).
Notation "'if' c 'then' t 'else' f" := (ite c t f) (in custom expr at level 1,
                                                       c custom expr at level 2,
                                                       t custom expr at level 4,
                                                       f custom expr at level 4).

(* Naturals *)
Notation "'0'" := zero (in custom expr).
Notation "'1'" := (succ zero) (in custom expr).
Notation "'s' t" := (succ t) (in custom expr at level 2,
                                 t custom expr).
Notation " t 'match'  '|' t1 '|' t2 'end'" := (tmatch t t1 t2) (in custom expr at level 2,
                                                              t1 custom expr at level 4,
                                                              t2 custom expr).

(* Fix points *)
(* Notation "'fix' t" := (notype_tfix t) (in custom expr at level 2,
                                          t custom expr).
*)
(* Let expression *)
Notation "'let' := t1 'in' t2" := (notype_tlet t1 t2) (in custom expr at level 1,
                                                       t1 custom expr at level 4,
                                                       t2 custom expr at level 4).
(* Sum *)
Notation "'right' ( t )" := (tright t) (in custom expr at level 2,
                                         t custom expr at level 4).
Notation "'left' ( t )" := (tleft t) (in custom expr at level 2,
                                         t custom expr at level 4).
Notation "t 'match' '|' 'left' => t1 '|' 'right' => t2 'end'" := (sum_match t t1 t2) (in custom expr at level 2,
                                                                                       t custom expr,
                                                                                       t1 custom expr,
                                                                                       t2 custom expr).

Notation "'fun' [ T ] => y" := (lambda T y) (in custom expr at level 4,
                                               T custom type at level 4,
                                               y custom expr at level 4).

Definition fresh_id (t: tree) := makeFresh (fv t :: nil).

Notation "'fun' ( x ) => t" :=
   (let fresh := (S (let x := (fvar 0 term_var) in (max (fv t)))) in 
    let x     := (fvar fresh term_var) in
    notype_lambda (close 0 t fresh))
     (in custom expr at level 100, x ident, t custom expr).

Eval compute in [| fun ( x ) => x |].

  (*
Notation "'fun' ( x ) => t" :=
   (let fresh := fresh_id (let x := (fvar 0 term_var) in t) in
   ((fun x => (fvar fresh term_var))
   (notype_lambda (close 0 t fresh)))) (in custom expr at level 100, x ident, t custom expr). *)

Eval compute in [| fun ( x ) => (fun (y) => x) |].
Example test1 : [| fun ( x ) => (x, (fun (y) => (x, y)), x) |] = [| fun => ((lt{0}, (fun => (lt{1}, lt{0}))), lt{0}) |].
Proof.
  unfold fv, pfv, max.
  simpl.
  assert (forall t:nat, (if tag_eq_dec term_var term_var then singleton t else nil) = (singleton t)) as H. {
    destruct (tag_eq_dec term_var term_var) eqn:E.
    reflexivity.
    congruence. }
  rewrite ?H.
  simpl.
  reflexivity.
Qed.

Eval compute in [| fun ( x ) => (fun (y) => x)|].

Notation "'def_rec' f '(' x ')' := t" :=
  (let f := (fvar 1000 term_var) in
   let x := (fvar 999 term_var) in
   (notype_tfix (close 0 (close 1 t 999) 1000)))
  (in custom expr at level 100, f ident, x ident, t custom expr, right associativity).



Eval compute in [|
     fun (x) => (fun (y) => ((x,y), fun(z) => (x, y))) |].

Eval compute in [|
(
def_rec plus(pair) :=
  pair._1 match
    | pair._2
    | fun(x) => s (plus (x, pair._2))
  end
) (0, 0)
|].

Notation "'λ' f" := (notype_lambda (close 0 (f (fvar 1000 term_var)) 1000))
  (at level 300, right associativity).

Eval compute in (λ (fun x => (pp x (notype_lambda x)))).
(* Examples *)
(* --------------------------------------------------------------------- *)

(* Unset Printing Notations. *)

Example ex1: wf [| if true then 0 else 1 |] 0.
Proof. repeat step. Qed.

Example ex2: wf [|
                 fun => lt{0} match
                       | left => 0
                       | right => 1 end
                |] 0.
Proof. repeat step. Qed.

Example ex3: wf [|
                 fun => let := (s 1) in
                     if lt{0} then (
                         lt{1} match
                           | 1
                           | (fun => (s lt{2})) end)
                     else (
                         let := 0 in ()
                       )
                 |] 0.
Proof. repeat step. Qed.

(* close free variable -> local variable *)


Compute tree_size [|
         let zero := s 0 in lt{0} match
         | s 0
             | s (s 0) end
|].


Compute close 0 (notype_lambda ((fvar 5 term_var))) 5.









