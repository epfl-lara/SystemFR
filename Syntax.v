Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import PeanoNat.

Require Export SystemFR.AssocList.
Require Export SystemFR.Trees.

Close Scope string_scope.

Lemma tag_eq_dec:
  forall tag1 tag2: fv_tag, { tag1 = tag2 } + { tag1 <> tag2 }.
Proof.
  intros.
  decide equality.
Qed.

Lemma op_eq_dec:
  forall o1 o2: op, { o1 = o2 } + { o1 <> o2 }.
Proof.
  intros.
  decide equality.
Defined.


Fixpoint pfv t tag: list nat :=
  match t with
  | fvar y tag' =>
    if (tag_eq_dec tag tag')
    then singleton y
    else nil
  | lvar _ _ => nil
  | notype_err => nil
  | err T => pfv T tag

  | uu => nil

  | tsize t => pfv t tag

  | notype_lambda t' => pfv t' tag
  | lambda T t' => pfv T tag ++ pfv t' tag
  | app t1 t2 => pfv t1 tag ++ pfv t2 tag

  | forall_inst t1 t2 => pfv t1 tag ++ pfv t2 tag

  | type_abs t => pfv t tag
  | type_inst t T => pfv t tag ++ pfv T tag

  | pp t1 t2 => pfv t1 tag ++ pfv t2 tag
  | pi1 t' => pfv t' tag
  | pi2 t' => pfv t' tag

  | because t1 t2 => pfv t1 tag ++ pfv t2 tag
  | get_refinement_witness t1 t2 => pfv t1 tag ++ pfv t2 tag

  | ttrue => nil
  | tfalse => nil
  | ite t1 t2 t3 => pfv t1 tag ++ pfv t2 tag ++ pfv t3 tag
  | boolean_recognizer _ t => pfv t tag

  | zero => nil
  | succ t' => pfv t' tag
  | tmatch t' t0 ts => pfv t' tag ++ pfv t0 tag ++ pfv ts tag

  | unary_primitive _ t => pfv t tag
  | binary_primitive _ t1 t2 => pfv t1 tag ++ pfv t2 tag

  | tfix T t' => pfv T tag ++ pfv t' tag
  | notype_tfix t' => pfv t' tag

  | notype_tlet t1 t2 => pfv t1 tag ++  pfv t2 tag
  | tlet t1 A t2 => pfv t1 tag ++ pfv A tag ++  pfv t2 tag
  | trefl t1 t2 => pfv t1 tag ++ pfv t2 tag

  | tfold T t' => pfv T tag ++ pfv t' tag
  | tunfold t' => pfv t' tag
  | tunfold_in t1 t2 => pfv t1 tag ++ pfv t2 tag
  | tunfold_pos_in t1 t2 => pfv t1 tag ++ pfv t2 tag

  | tleft t' => pfv t' tag
  | tright t' => pfv t' tag
  | sum_match t' tl tr => pfv t' tag ++ pfv tl tag ++ pfv tr tag

  | typecheck t T => pfv t tag ++ pfv T tag

  | T_unit => nil
  | T_bool => nil
  | T_nat => nil
  | T_refine A p => pfv A tag ++ pfv p tag
  | T_type_refine A B => pfv A tag ++ pfv B tag
  | T_prod A B => pfv A tag ++ pfv B tag
  | T_arrow A B => pfv A tag ++ pfv B tag
  | T_sum A B => pfv A tag ++ pfv B tag
  | T_intersection A B => pfv A tag ++ pfv B tag
  | T_union A B => pfv A tag ++ pfv B tag
  | T_top => nil
  | T_bot => nil
  | T_equiv t1 t2 => pfv t1 tag ++ pfv t2 tag
  | T_forall A B => pfv A tag ++ pfv B tag
  | T_exists A B => pfv A tag ++ pfv B tag
  | T_abs T => pfv T tag
  | T_rec n T0 Ts => pfv n tag ++ pfv T0 tag ++ pfv Ts tag
  end.

Definition fv t := pfv t term_var.
Definition tfv t := pfv t type_var.

Hint Unfold fv tfv: core.

Definition tvar_list := list nat.

Definition context: Type := list (nat * tree).

Fixpoint pfv_context Γ tag :=
  match Γ with
  | nil => nil
  | (x,T) :: Γ' => x :: pfv T tag ++ pfv_context Γ' tag
  end.

Definition fv_context Γ := pfv_context Γ term_var.

Hint Unfold fv_context: core.

Lemma fv_context_append:
  forall Γ1 Γ2 tag,
    pfv_context (Γ1 ++ Γ2) tag = pfv_context Γ1 tag ++ pfv_context Γ2 tag.
Proof.
  induction Γ1; repeat step || rewrite app_assoc_reverse.
Qed.

Hint Rewrite fv_context_append: list_utils.

Fixpoint pfv_range (m: list (nat * tree)) tag :=
  match m with
  | nil => nil
  | (x,t) :: m' => pfv t tag ++ pfv_range m' tag
  end.

Definition fv_range (m: list (nat * tree)) := pfv_range m term_var.

Hint Unfold fv_range: core.

Fixpoint pclosed_mapping (m: list (nat * tree)) tag: Prop :=
  match m with
  | nil => True
  | (x,t) :: m' => pfv t tag = nil /\ pclosed_mapping m' tag
  end.

Definition closed_mapping (m: list (nat * tree)): Prop := pclosed_mapping m term_var.

Hint Unfold closed_mapping: core.

Fixpoint psubstitute t (l: list (nat * tree)) (tag: fv_tag): tree :=
  match t with
  | fvar x tag' =>
    match lookup PeanoNat.Nat.eq_dec l x with
    | None => t
    | Some e =>
      if (tag_eq_dec tag tag')
      then e
      else t
    end

  | lvar _ _ => t
  | notype_err => t
  | err T => err (psubstitute T l tag)

  | uu => t

  | tsize t => tsize (psubstitute t l tag)

  | notype_lambda t' => notype_lambda (psubstitute t' l tag)
  | lambda T t' => lambda (psubstitute T l tag) (psubstitute t' l tag)
  | app t1 t2 => app (psubstitute t1 l tag) (psubstitute t2 l tag)

  | forall_inst t1 t2 => forall_inst (psubstitute t1 l tag) (psubstitute t2 l tag)

  | type_abs t' => type_abs (psubstitute t' l tag)
  | type_inst t' T => type_inst (psubstitute t' l tag) (psubstitute T l tag)

  | pp t1 t2 => pp (psubstitute t1 l tag) (psubstitute t2 l tag)
  | pi1 t' => pi1 (psubstitute t' l tag)
  | pi2 t' => pi2 (psubstitute t' l tag)

  | because t1 t2 => because (psubstitute t1 l tag) (psubstitute t2 l tag)
  | get_refinement_witness t1 t2 => get_refinement_witness (psubstitute t1 l tag) (psubstitute t2 l tag)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (psubstitute t1 l tag) (psubstitute t2 l tag) (psubstitute t3 l tag)
  | boolean_recognizer r t => boolean_recognizer r (psubstitute t l tag)

  | zero => t
  | succ t' => succ (psubstitute t' l tag)
  | tmatch t' t1 t2 => tmatch (psubstitute t' l tag) (psubstitute t1 l tag) (psubstitute t2 l tag)

  | unary_primitive o t => unary_primitive o (psubstitute t l tag)
  | binary_primitive o t1 t2 => binary_primitive o (psubstitute t1 l tag) (psubstitute t2 l tag)

  | tfix T t' => tfix (psubstitute T l tag) (psubstitute t' l tag)
  | notype_tfix t' => notype_tfix (psubstitute t' l tag)

  | notype_tlet t1 t2 => notype_tlet (psubstitute t1 l tag) (psubstitute t2 l tag)
  | tlet t1 T t2 => tlet (psubstitute t1 l tag) (psubstitute T l tag) (psubstitute t2 l tag)
  | trefl t1 t2 => trefl (psubstitute t1 l tag) (psubstitute t2 l tag)

  | tfold T t' => tfold (psubstitute T l tag) (psubstitute t' l tag)
  | tunfold t' => tunfold (psubstitute t' l tag)
  | tunfold_in t1 t2 => tunfold_in (psubstitute t1 l tag) (psubstitute t2 l tag)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (psubstitute t1 l tag) (psubstitute t2 l tag)

  | tleft t' => tleft (psubstitute t' l tag)
  | tright t' => tright (psubstitute t' l tag)
  | sum_match t' tl tr => sum_match (psubstitute t' l tag) (psubstitute tl l tag) (psubstitute tr l tag)

  | typecheck t T => typecheck (psubstitute t l tag) (psubstitute T l tag)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_arrow T1 T2 => T_arrow (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_sum T1 T2 => T_sum (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_refine T p => T_refine (psubstitute T l tag) (psubstitute p l tag)
  | T_type_refine T1 T2 => T_type_refine (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_intersection T1 T2 => T_intersection (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_union T1 T2 => T_union (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (psubstitute t1 l tag) (psubstitute t2 l tag)
  | T_forall T1 T2 => T_forall (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_exists T1 T2 => T_exists (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_abs T => T_abs (psubstitute T l tag)
  | T_rec n T0 Ts => T_rec (psubstitute n l tag) (psubstitute T0 l tag) (psubstitute Ts l tag)
  end.

Definition substitute t l := psubstitute t l term_var.
Definition substitute_type_vars t l := psubstitute t l type_var.

Hint Unfold substitute: core.
Hint Unfold substitute_type_vars: core.

Fixpoint psubstitute_context (Γ: context) (l: list (nat * tree)) tag: context :=
  match Γ with
  | nil => nil
  | (x,T) :: Γ' => (x, psubstitute T l tag) :: psubstitute_context Γ' l tag
  end.

Definition substitute_context (Γ: context) (l: list (nat * tree)): context :=
  psubstitute_context Γ l term_var.

Fixpoint wf t k :=
  match t with
  | fvar _ _ => True
  | lvar i term_var => i < k
  | lvar i type_var => True

  | notype_err => True
  | err T => wf T k

  | uu => True

  | tsize t => wf t k

  | notype_lambda t' => wf t' (S k)
  | lambda T t' => wf T k /\ wf t' (S k)
  | app t1 t2 => wf t1 k /\ wf t2 k

  | forall_inst t1 t2 => wf t1 k /\ wf t2 k

  | type_abs t => wf t k
  | type_inst t T => wf t k /\ wf T k

  | pp t1 t2 => wf t1 k /\ wf t2 k
  | pi1 t => wf t k
  | pi2 t => wf t k

  | because t1 t2 => wf t1 k /\ wf t2 k
  | get_refinement_witness t1 t2 => wf t1 k /\ wf t2 (S k)

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => wf t1 k /\ wf t2 k /\ wf t3 k
  | boolean_recognizer _ t => wf t k

  | zero => True
  | succ t' => wf t' k
  | tmatch t' t1 t2 =>
      wf t' k /\
      wf t1 k /\
      wf t2 (S k)

  | unary_primitive _ t => wf t k
  | binary_primitive _ t1 t2 => wf t1 k /\ wf t2 k

  | tfix T t' => wf T (S k) /\ wf t' (S (S k))
  | notype_tfix t' => wf t' (S (S k))

  | notype_tlet t1 t2 => wf t1 k /\ wf t2 (S k)
  | tlet t1 T t2 => wf t1 k /\ wf T k /\ wf t2 (S k)

  | trefl t1 t2 => wf t1 k /\ wf t2 k

  | tfold T t' => wf T k /\ wf t' k
  | tunfold t' => wf t' k
  | tunfold_in t1 t2 => wf t1 k /\ wf t2 (S k)
  | tunfold_pos_in t1 t2 => wf t1 k /\ wf t2 (S k)

  | tleft t' => wf t' k
  | tright t' => wf t' k
  | sum_match t' tl tr => wf t' k /\ wf tl (S k) /\ wf tr (S k)

  | typecheck t T => wf t k /\ wf T k

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_arrow T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_sum T1 T2 => wf T1 k /\ wf T2 k
  | T_refine T p => wf T k /\ wf p (S k)
  | T_type_refine T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_intersection T1 T2 => wf T1 k /\ wf T2 k
  | T_union T1 T2 => wf T1 k /\ wf T2 k
  | T_top => True
  | T_bot => True
  | T_equiv t1 t2 => wf t1 k /\ wf t2 k
  | T_forall T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_exists T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_abs T => wf T k
  | T_rec n T0 Ts => wf n k /\ wf T0 k /\ wf Ts k
  end.

Fixpoint twf t k :=
  match t with
  | fvar _ _ => True
  | lvar i type_var => i < k
  | lvar i term_var => True

  | err T => twf T k
  | notype_err => True

  | uu => True

  | tsize t => twf t k

  | notype_lambda t' => twf t' k
  | lambda T t' => twf T k /\ twf t' k
  | app t1 t2 => twf t1 k /\ twf t2 k

  | forall_inst t1 t2 => twf t1 k /\ twf t2 k

  | type_abs t => twf t (S k)
  | type_inst t T => twf t k /\ twf T k

  | pp t1 t2 => twf t1 k /\ twf t2 k
  | pi1 t => twf t k
  | pi2 t => twf t k

  | because t1 t2 => twf t1 k /\ twf t2 k
  | get_refinement_witness t1 t2 => twf t1 k /\ twf t2 k

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => twf t1 k /\ twf t2 k /\ twf t3 k
  | boolean_recognizer _ t => twf t k

  | zero => True
  | succ t' => twf t' k
  | tmatch t' t1 t2 =>
      twf t' k /\
      twf t1 k /\
      twf t2 k

  | unary_primitive _ t => twf t k
  | binary_primitive _ t1 t2 => twf t1 k /\ twf t2 k

  | tfix T t' => twf T k /\ twf t' k
  | notype_tfix t' => twf t' k

  | notype_tlet t1 t2 => twf t1 k /\ twf t2 k
  | tlet t1 T t2 => twf t1 k /\ twf T k /\ twf t2 k

  | trefl t1 t2 => twf t1 k /\ twf t2 k

  | tfold T t => twf T k /\ twf t k
  | tunfold t => twf t k
  | tunfold_in t1 t2 => twf t1 k /\ twf t2 k
  | tunfold_pos_in t1 t2 => twf t1 k /\ twf t2 k

  | tleft t => twf t k
  | tright t => twf t k
  | sum_match t' tl tr => twf t' k /\ twf tl k /\ twf tr k

  | typecheck t T => twf t k /\ twf T k

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => twf T1 k /\ twf T2 k
  | T_arrow T1 T2 => twf T1 k /\ twf T2 k
  | T_sum T1 T2 => twf T1 k /\ twf T2 k
  | T_refine T p => twf T k /\ twf p k
  | T_type_refine T1 T2 => twf T1 k /\ twf T2 k
  | T_intersection T1 T2 => twf T1 k /\ twf T2 k
  | T_union T1 T2 => twf T1 k /\ twf T2 k
  | T_top => True
  | T_bot => True
  | T_equiv t1 t2 => twf t1 k /\ twf t2 k
  | T_forall T1 T2 => twf T1 k /\ twf T2 k
  | T_exists T1 T2 => twf T1 k /\ twf T2 k
  | T_abs T => twf T (S k)
  | T_rec n T0 Ts => twf n k /\ twf T0 k /\ twf Ts (S k)
  end.

Fixpoint wfs (Γ: list (nat * tree)) k :=
  match Γ with
  | nil => True
  | (x,A) :: Γ' => wf A k /\ wfs Γ' k
  end.

Fixpoint twfs (Γ: list (nat * tree)) k :=
  match Γ with
  | nil => True
  | (x,A) :: Γ' => twf A k /\ twfs Γ' k
  end.

Fixpoint open (k: nat) (t rep: tree) :=
  match t with
  | fvar _ _ => t
  | lvar i term_var => if (PeanoNat.Nat.eq_dec k i) then rep else t
  | lvar i type_var => t
  | notype_err => t
  | err T => err (open k T rep)

  | notype_lambda t' => notype_lambda (open (S k) t' rep)
  | lambda T t' => lambda (open k T rep) (open (S k) t' rep)
  | app t1 t2 => app (open k t1 rep) (open k t2 rep)

  | forall_inst t1 t2 => forall_inst (open k t1 rep) (open k t2 rep)

  | type_abs t => type_abs (open k t rep)
  | type_inst t T => type_inst (open k t rep) (open k T rep)

  | uu => t

  | tsize t => tsize (open k t rep)

  | pp t1 t2 => pp (open k t1 rep) (open k t2 rep)
  | pi1 t => pi1 (open k t rep)
  | pi2 t => pi2 (open k t rep)

  | because t1 t2 => because (open k t1 rep) (open k t2 rep)
  | get_refinement_witness t1 t2 => get_refinement_witness (open k t1 rep) (open (S k) t2 rep)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (open k t1 rep) (open k t2 rep) (open k t3 rep)
  | boolean_recognizer r t => boolean_recognizer r (open k t rep)

  | zero => t
  | succ t' => succ (open k t' rep)
  | tmatch t' t1 t2 =>
      tmatch
          (open k t' rep)
          (open k t1 rep)
          (open (S k) t2 rep)

  | unary_primitive o t => unary_primitive o (open k t rep)
  | binary_primitive o t1 t2 => binary_primitive o (open k t1 rep) (open k t2 rep)

  | tfix T t' => tfix (open (S k) T rep) (open (S (S k)) t' rep)
  | notype_tfix t' => notype_tfix (open (S (S k)) t' rep)

  | notype_tlet t1 t2 =>
      notype_tlet (open k t1 rep) (open (S k) t2 rep)
  | tlet t1 T t2 =>
      tlet (open k t1 rep) (open k T rep) (open (S k) t2 rep)
  | trefl t1 t2 => trefl (open k t1 rep) (open k t2 rep)

  | tfold T t' => tfold (open k T rep) (open k t' rep)
  | tunfold t' => tunfold (open k t' rep)
  | tunfold_in t1 t2 => tunfold_in (open k t1 rep) (open (S k) t2 rep)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (open k t1 rep) (open (S k) t2 rep)

  | tleft t' => tleft (open k t' rep)
  | tright t' => tright (open k t' rep)
  | sum_match t' tl tr => sum_match (open k t' rep) (open (S k) tl rep) (open (S k) tr rep)

  | typecheck t T => typecheck (open k t rep) (open k T rep)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (open k T1 rep) (open (S k) T2 rep)
  | T_arrow T1 T2 => T_arrow (open k T1 rep) (open (S k) T2 rep)
  | T_sum T1 T2 => T_sum (open k T1 rep) (open k T2 rep)
  | T_refine T p => T_refine (open k T rep) (open (S k) p rep)
  | T_type_refine T1 T2 => T_type_refine (open k T1 rep) (open (S k) T2 rep)
  | T_intersection T1 T2 => T_intersection (open k T1 rep) (open k T2 rep)
  | T_union T1 T2 => T_union (open k T1 rep) (open k T2 rep)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (open k t1 rep) (open k t2 rep)
  | T_forall T1 T2 => T_forall (open k T1 rep) (open (S k) T2 rep)
  | T_exists T1 T2 => T_exists (open k T1 rep) (open (S k) T2 rep)
  | T_abs T => T_abs (open k T rep)
  | T_rec n T0 Ts => T_rec (open k n rep) (open k T0 rep) (open k Ts rep)
  end.

Fixpoint close (k: nat) (t: tree) (x: nat) :=
  match t with
  | fvar y term_var => if (PeanoNat.Nat.eq_dec x y) then lvar k term_var else t
  | fvar _ type_var => t
  | lvar _ _ => t
  | notype_err => t
  | err T => err (close k T x)

  | notype_lambda t' => notype_lambda (close (S k) t' x)
  | lambda T t' => lambda (close k T x) (close (S k) t' x)
  | app t1 t2 => app (close k t1 x) (close k t2 x)

  | forall_inst t1 t2 => forall_inst (close k t1 x) (close k t2 x)

  | type_abs t => type_abs (close k t x)
  | type_inst t T => type_inst (close k t x) (close k T x)

  | uu => t

  | tsize t => tsize (close k t x)

  | pp t1 t2 => pp (close k t1 x) (close k t2 x)
  | pi1 t => pi1 (close k t x)
  | pi2 t => pi2 (close k t x)

  | because t1 t2 => because (close k t1 x) (close k t2 x)
  | get_refinement_witness t1 t2 => get_refinement_witness (close k t1 x) (close (S k) t2 x)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (close k t1 x) (close k t2 x) (close k t3 x)
  | boolean_recognizer r t => boolean_recognizer r (close k t x)

  | zero => t
  | succ t' => succ (close k t' x)
  | tmatch t' t1 t2 =>
      tmatch
          (close k t' x)
          (close k t1 x)
          (close (S k) t2 x)

  | unary_primitive o t => unary_primitive o (close k t x)
  | binary_primitive o t1 t2 => binary_primitive o (close k t1 x) (close k t2 x)

  | tfix T t' => tfix (close (S k) T x) (close (S (S k)) t' x)
  | notype_tfix t' => notype_tfix (close (S (S k)) t' x)

  | notype_tlet t1 t2 =>
      notype_tlet (close k t1 x) (close (S k) t2 x)
  | tlet t1 T t2 =>
      tlet (close k t1 x) (close k T x) (close (S k) t2 x)
  | trefl t1 t2 => trefl (close k t1 x) (close k t2 x)

  | tfold T t' => tfold (close k T x) (close k t' x)
  | tunfold t' => tunfold (close k t' x)
  | tunfold_in t1 t2 => tunfold_in (close k t1 x) (close (S k) t2 x)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (close k t1 x) (close (S k) t2 x)

  | tleft t' => tleft (close k t' x)
  | tright t' => tright (close k t' x)
  | sum_match t' tl tr => sum_match (close k t' x) (close (S k) tl x) (close (S k) tr x)

  | typecheck t T => typecheck (close k t x) (close k T x)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (close k T1 x) (close (S k) T2 x)
  | T_arrow T1 T2 => T_arrow (close k T1 x) (close (S k) T2 x)
  | T_sum T1 T2 => T_sum (close k T1 x) (close k T2 x)
  | T_refine T p => T_refine (close k T x) (close (S k) p x)
  | T_type_refine T1 T2 => T_type_refine (close k T1 x) (close (S k) T2 x)
  | T_intersection T1 T2 => T_intersection (close k T1 x) (close k T2 x)
  | T_union T1 T2 => T_union (close k T1 x) (close k T2 x)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (close k t1 x) (close k t2 x)
  | T_forall T1 T2 => T_forall (close k T1 x) (close (S k) T2 x)
  | T_exists T1 T2 => T_exists (close k T1 x) (close (S k) T2 x)
  | T_abs T => T_abs (close k T x)
  | T_rec n T0 Ts => T_rec (close k n x) (close k T0 x) (close k Ts x)
  end.

Fixpoint topen (k: nat) (t rep: tree) :=
  match t with
  | fvar _ _ => t
  | lvar i type_var => if (PeanoNat.Nat.eq_dec k i) then rep else t
  | lvar i term_var => t

  | notype_err => t
  | err T => err (topen k T rep)

  | notype_lambda t' => notype_lambda (topen k t' rep)
  | lambda T t' => lambda (topen k T rep) (topen k t' rep)
  | app t1 t2 => app (topen k t1 rep) (topen k t2 rep)

  | forall_inst t1 t2 => forall_inst (topen k t1 rep) (topen k t2 rep)

  | type_abs t => type_abs (topen (S k) t rep)
  | type_inst t T => type_inst (topen k t rep) (topen k T rep)

  | uu => t

  | tsize t => tsize (topen k t rep)

  | pp t1 t2 => pp (topen k t1 rep) (topen k t2 rep)
  | pi1 t => pi1 (topen k t rep)
  | pi2 t => pi2 (topen k t rep)

  | because t1 t2 => because (topen k t1 rep) (topen k t2 rep)
  | get_refinement_witness t1 t2 => get_refinement_witness (topen k t1 rep) (topen k t2 rep)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (topen k t1 rep) (topen k t2 rep) (topen k t3 rep)
  | boolean_recognizer r t => boolean_recognizer r (topen k t rep)

  | zero => t
  | succ t' => succ (topen k t' rep)
  | tmatch t' t1 t2 =>
      tmatch
          (topen k t' rep)
          (topen k t1 rep)
          (topen k t2 rep)

  | unary_primitive o t => unary_primitive o (topen k t rep)
  | binary_primitive o t1 t2 => binary_primitive o (topen k t1 rep) (topen k t2 rep)

  | tfix T t' => tfix (topen k T rep) (topen k t' rep)
  | notype_tfix t' => notype_tfix (topen k t' rep)

  | notype_tlet t1 t2 =>
      notype_tlet (topen k t1 rep) (topen k t2 rep)
  | tlet t1 T t2 =>
      tlet (topen k t1 rep) (topen k T rep) (topen k t2 rep)

  | trefl t1 t2 => trefl (topen k t1 rep) (topen k t2 rep)

  | tfold T t => tfold (topen k T rep) (topen k t rep)
  | tunfold t => tunfold (topen k t rep)
  | tunfold_in t1 t2 => tunfold_in (topen k t1 rep) (topen k t2 rep)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (topen k t1 rep) (topen k t2 rep)

  | tleft t' => tleft (topen k t' rep)
  | tright t' => tright (topen k t' rep)
  | sum_match t' tl tr => sum_match (topen k t' rep) (topen k tl rep) (topen k tr rep)

  | typecheck t T => typecheck (topen k t rep) (topen k T rep)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (topen k T1 rep) (topen k T2 rep)
  | T_arrow T1 T2 => T_arrow (topen k T1 rep) (topen k T2 rep)
  | T_sum T1 T2 => T_sum (topen k T1 rep) (topen k T2 rep)
  | T_refine T p => T_refine (topen k T rep) (topen k p rep)
  | T_type_refine T1 T2 => T_type_refine (topen k T1 rep) (topen k T2 rep)
  | T_intersection T1 T2 => T_intersection (topen k T1 rep) (topen k T2 rep)
  | T_union T1 T2 => T_union (topen k T1 rep) (topen k T2 rep)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (topen k t1 rep) (topen k t2 rep)
  | T_forall T1 T2 => T_forall (topen k T1 rep) (topen k T2 rep)
  | T_exists T1 T2 => T_exists (topen k T1 rep) (topen k T2 rep)
  | T_abs T => T_abs (topen (S k) T rep)
  | T_rec n T0 Ts => T_rec (topen k n rep) (topen k T0 rep) (topen (S k) Ts rep)
  end.

Fixpoint tclose (k: nat) (t: tree) (x: nat) :=
  match t with
  | fvar _ term_var => t
  | fvar y type_var => if (PeanoNat.Nat.eq_dec y x) then lvar k type_var else t
  | lvar i _ => t

  | err T => err (tclose k T x)
  | notype_err => t

  | notype_lambda t' => notype_lambda (tclose k t' x)
  | lambda T t' => lambda (tclose k T x) (tclose k t' x)
  | app t1 t2 => app (tclose k t1 x) (tclose k t2 x)

  | forall_inst t1 t2 => forall_inst (tclose k t1 x) (tclose k t2 x)

  | type_abs t => type_abs (tclose (S k) t x)
  | type_inst t T => type_inst (tclose k t x) (tclose k T x)

  | uu => t

  | tsize t => tsize (tclose k t x)

  | pp t1 t2 => pp (tclose k t1 x) (tclose k t2 x)
  | pi1 t => pi1 (tclose k t x)
  | pi2 t => pi2 (tclose k t x)

  | because t1 t2 => because (tclose k t1 x) (tclose k t2 x)
  | get_refinement_witness t1 t2 => get_refinement_witness (tclose k t1 x) (tclose k t2 x)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (tclose k t1 x) (tclose k t2 x) (tclose k t3 x)
  | boolean_recognizer r t => boolean_recognizer r (tclose k t x)

  | zero => t
  | succ t' => succ (tclose k t' x)
  | tmatch t' t1 t2 =>
      tmatch
          (tclose k t' x)
          (tclose k t1 x)
          (tclose k t2 x)

  | unary_primitive o t => unary_primitive o (tclose k t x)
  | binary_primitive o t1 t2 => binary_primitive o (tclose k t1 x) (tclose k t2 x)

  | tfix T t' => tfix (tclose k T x) (tclose k t' x)
  | notype_tfix t' => notype_tfix (tclose k t' x)

  | notype_tlet t1 t2 =>
      notype_tlet (tclose k t1 x) (tclose k t2 x)
  | tlet t1 T t2 =>
      tlet (tclose k t1 x) (tclose k T x) (tclose k t2 x)
  | trefl t1 t2 => trefl (tclose k t1 x) (tclose k t2 x)

  | tfold T t => tfold (tclose k T x) (tclose k t x)
  | tunfold t => tunfold (tclose k t x)
  | tunfold_in t1 t2 => tunfold_in (tclose k t1 x) (tclose k t2 x)
  | tunfold_pos_in t1 t2 => tunfold_pos_in (tclose k t1 x) (tclose k t2 x)

  | tleft t' => tleft (tclose k t' x)
  | tright t' => tright (tclose k t' x)
  | sum_match t' tl tr => sum_match (tclose k t' x) (tclose k tl x) (tclose k tr x)

  | typecheck t T => typecheck (tclose k t x) (tclose k T x)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (tclose k T1 x) (tclose k T2 x)
  | T_arrow T1 T2 => T_arrow (tclose k T1 x) (tclose k T2 x)
  | T_sum T1 T2 => T_sum (tclose k T1 x) (tclose k T2 x)
  | T_refine T p => T_refine (tclose k T x) (tclose k p x)
  | T_type_refine T1 T2 => T_type_refine (tclose k T1 x) (tclose k T2 x)
  | T_intersection T1 T2 => T_intersection (tclose k T1 x) (tclose k T2 x)
  | T_union T1 T2 => T_union (tclose k T1 x) (tclose k T2 x)
  | T_top => t
  | T_bot => t
  | T_equiv t1 t2 => T_equiv (tclose k t1 x) (tclose k t2 x)
  | T_forall T1 T2 => T_forall (tclose k T1 x) (tclose k T2 x)
  | T_exists T1 T2 => T_exists (tclose k T1 x) (tclose k T2 x)
  | T_abs T => T_abs (tclose (S k) T x)
  | T_rec n T0 Ts => T_rec (tclose k n x) (tclose k T0 x) (tclose (S k) Ts x)
  end.
