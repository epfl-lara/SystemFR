Require Export SystemFR.Trees.
Require Export SystemFR.Syntax.
Require Export SystemFR.Freshness.


Open Scope list.

Declare Custom Entry expr.
Declare Custom Entry type.

(* Entry point *)

Notation "'|' t" := (fun (fv_id:nat) => t) (at level 200).
Notation "[| x |]" := (x 0) (x custom expr at level 2).
Notation "( x )" := (fun (fv_id:nat) => (x fv_id)) (in custom expr, x custom expr).
Notation "x" := (fun fv_id => x) (in custom expr at level 0, x ident). 

(* Variables (nameless) *)
Notation "'ft{' v '}'" := (| (fvar v term_var)) (in custom expr,
                                                v constr).
Notation "'lt{' v '}'" := (| (lvar v term_var)) (in custom expr,
                                                v constr).


Notation "( t1 , t2 )" :=
  (fun fv_id => (pp (t1 fv_id) (t2 fv_id)))
  (in custom expr, t1 custom expr, t2 custom expr).

Notation "'0'" := (| zero) (in custom expr).

Notation "'fun' => t" :=
     (fun fv_id => (
          (notype_lambda (t fv_id))))
     (in custom expr at level 100, t custom expr).
Notation "'fun' ( x ) => t" :=
     (fun fv_id => (
          let x := (fvar fv_id term_var) in
          (notype_lambda (close 0 (t (S fv_id)) fv_id))))
     (in custom expr at level 100, x ident, t custom expr).

Notation "'fun' f ( x ) => t" :=
     (fun fv_id => (
          let x := (fvar fv_id term_var) in
          (notype_lambda (close 0 (t (S fv_id)) fv_id))))
     (in custom expr at level 100, f ident, x ident, t custom expr).

Notation "'def_rec' f x => t":=
     (fun fv_id => (
        let f := (fvar fv_id term_var) in
        let x := (fvar (S fv_id) term_var) in
        (notype_tfix (close 0 (notype_lambda (close 0 (t (S (S fv_id))) (S fv_id))) fv_id) )))
     (in custom expr at level 100, f ident, x ident, t custom expr).

Notation "'def_rec' f x y => t":=
     (fun fv_id => (
          let f := (fvar fv_id term_var) in
          let x := (fvar (S fv_id) term_var) in
          let y := (fvar (S (S fv_id)) term_var) in
          (notype_tfix (
             close 0 (
               notype_lambda (
                 close 0 (
                    notype_lambda (
                        close 0 (
                          t (S(S(S fv_id))))
                        (S (S fv_id))))
                 (S fv_id)))
             fv_id))))
     (in custom expr at level 100, f ident, x ident, y ident, t custom expr).

Notation " t1 t2 " :=
  (fun fv_id => (app (t1 fv_id) (t2 fv_id)))
    (in custom expr at level 200, right associativity,
        t1 custom expr,
        t2 custom expr).

Eval compute in [| fun f (x) => (fun g (y) => (x,y)) |].

Eval compute in [| def_rec plus x y => ((plus, x), y) |].
Eval compute in [| fun set_left (x) => (x, 0) |].
Eval compute in [| fun truc(x) => (fun truc2(y) => (fun truc3(z) => ((x,y),z))) |].

Eval compute in [| ((ft{0}, 0), 0) |].

(* Untyped language *)
(* --------------------------------------------------------------------- *)

Notation "'()'" := (|uu) (in custom expr).

Eval compute in [| () |].

Notation "'size' ( t )" := (fun fv_id => (tsize (t fv_id))) (in custom expr,
                                         t custom expr).

(* Pairs *)

Notation "t '._1'" := (fun fv_id => (pi1 (t fv_id))) (in custom expr at level 200,
                                  t custom expr).
Notation "t '._2'" := (fun fv_id => (pi2 (t fv_id))) (in custom expr at level 200,
                                  t custom expr).

(* Booleans *)
Notation "'true'" := (|ttrue) (in custom expr).
Notation "'false'" := (|tfalse) (in custom expr).
Notation "'if' c 'then' t 'else' f" := (fun fv_id => (ite (c fv_id) (t fv_id) (f fv_id))) (in custom expr at level 1,
                                                       c custom expr,
                                                       t custom expr,
                                                       f custom expr).

(* Naturals *)
Notation "'1'" := (| (succ zero)) (in custom expr).
Notation "'s' t" := (fun fv_id => (succ (t fv_id))) (in custom expr at level 2,
                                 t custom expr).

Notation "'match' t 'with' '|' '0' => t1 '|' 's' x => t2 'end'" :=
  (fun (fv_id:nat) => (
       tmatch (t fv_id)
              (t1 fv_id)
              (let x := (fvar fv_id term_var) in (close 0 (t2 (S fv_id)) fv_id))))
  (in custom expr at level 190,
      t custom expr,
      t1 custom expr,
      t2 custom expr,
      x ident).

Eval compute in
    [| match 0 with
         |0 => 1
         |s n => (
            match n with
            | 0 => 0
            | s n' => n' end) end |].

Definition sfr_plus := [|
 def_rec plus x y =>
 (match x with
     | 0 => y
     | s x' => (plus x' y) end)
|].

Example ex1 : wf sfr_plus 0.
Proof.
  repeat step.
Qed.

(* Let expression *)
Notation "'let' x := t1 'in' t2" :=
  (fun (fv_id : nat) => (
       notype_tlet (t1 fv_id)
                   (let x := (fvar fv_id term_var) in (close 0 (t2 (S fv_id)) fv_id) )))
    (in custom expr at level 190,
        t1 custom expr,
        t2 custom expr,
        x ident).

Check
    [| let n := 1 in (match n with
                                 | 0 => 1
                                 | s n' => (match n' with
                                             | 0 => 1
                                             | s n'' => ((n, n'),n'') end) end) |].

Eval compute in
[|
 let plus := (def_rec f x y => (match x with
                                    | 0 => y
                                    | s x' => (f x' y) end)) in (
 let fibo := (def_rec f n => (match n with
                                 | 0 => 1
                                 | s n' => (match n' with
                                             | 0 => 1
                                             | s n'' => plus (f n') (f n'') end) end))
                 in fibo (s (s (s (s (s 0))))))
|].


(* Sum *)
Notation "'right' t " :=
  (fun fv_id => tright (t fv_id))
  (in custom expr at level 180, right associativity, t custom expr).
Notation "'left' t " := 
  (fun fv_id => tleft (t fv_id))
  (in custom expr at level 180, right associativity, t custom expr).


Notation "'match' t 'with' '|' 'left' l => t1 '|' 'right' r => t2 'end'" :=
  (fun (fv_id:nat) => (
       tmatch (t fv_id)
              (let l  := (fvar fv_id term_var) in (close 0 (t1 (S fv_id)) fv_id))
              (let r := (fvar fv_id term_var) in (close 0 (t2 (S fv_id)) fv_id))))
  (in custom expr at level 190,
      t custom expr,
      t1 custom expr,
      t2 custom expr,
      l ident,
      r ident).

Eval compute in [| fun ( x ) => x |].

Eval compute in [| fun ( x ) => (fun (y) => x) |].
Example test1 : [| fun ( x ) => ((x, fun (y) => (x, y)), x) |] = [| fun => ((lt{0}, (fun => (lt{1}, lt{0}))), lt{0}) |].
Proof.
  repeat step.
  Qed.

Eval compute in [| fun ( x ) => (fun (y) => x)|].


Eval compute in [|
     fun (x) => (fun (y) => ((x,y), fun(z) => (x, y))) |].

(* Examples *)
(* --------------------------------------------------------------------- *)

(* Unset Printing Notations. *)

Example ex11: wf [| if true then 0 else 1 |] 0.
Proof. repeat step. Qed.

Example ex2: wf [|
                 fun => match lt{0} with
                       | left x => 0
                       | right x => 1 end
                |] 0.
Proof. repeat step. Qed.

Example ex3: wf [|
                 fun => let x := (s 1) in
                     if x then (
                         match 0 with
                           | 0 => 1
                           | s _ => x  end)
                     else (
                         let y := 0 in ()
                       )
                 |] 0.
Proof. repeat step. Qed.

(* close free variable -> local variable *)











