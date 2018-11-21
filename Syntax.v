Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import PeanoNat.

Require Import Termination.ListUtils.
Require Import Termination.AssocList.
Require Import Termination.Tactics.
Require Export Termination.Trees.
Require Import Termination.Sets.

Lemma tag_eq_dec:
  forall tag1 tag2: fv_tag, { tag1 = tag2 } + { tag1 <> tag2 }.
Proof.
  intros.
  decide equality.
Qed.

Fixpoint pfv t tag: set nat :=
  match t with
  | fvar y tag' =>
    if (tag_eq_dec tag tag')
    then singleton y
    else nil
  | lvar _ _ => nil
  | err => nil

  | uu => nil

  | notype_lambda t' => pfv t' tag
  | lambda T t' => pfv T tag ++ pfv t' tag
  | app t1 t2 => pfv t1 tag ++ pfv t2 tag

  | type_abs t => pfv t tag
  | type_inst t T => pfv t tag ++ pfv T tag
  | notype_inst t => pfv t tag

  | pp t1 t2 => pfv t1 tag ++ pfv t2 tag
  | pi1 t' => pfv t' tag
  | pi2 t' => pfv t' tag

  | ttrue => nil
  | tfalse => nil
  | ite t1 t2 t3 => pfv t1 tag ++ pfv t2 tag ++ pfv t3 tag

  | zero => nil
  | succ t' => pfv t' tag
  | notype_rec t' t0 ts => pfv t' tag ++ pfv t0 tag ++ pfv ts tag
  | rec T t' t0 ts => pfv T tag ++ pfv t' tag ++ pfv t0 tag ++ pfv ts tag
  | tmatch t' t0 ts => pfv t' tag ++ pfv t0 tag ++ pfv ts tag

  | tfix T t' => pfv T tag ++ pfv t' tag
  | notype_tfix t' => pfv t' tag

  | notype_tlet t1 t2 => pfv t1 tag ++  pfv t2 tag
  | tlet t1 A t2 => pfv t1 tag ++ pfv A tag ++  pfv t2 tag
  | trefl => nil

  | T_unit => nil
  | T_bool => nil
  | T_nat => nil
  | T_refine A p => pfv A tag ++ pfv p tag
  | T_prod A B => pfv A tag ++ pfv B tag
  | T_arrow A B => pfv A tag ++ pfv B tag
  | T_let t A B => pfv t tag ++ pfv A tag ++ pfv B tag
  | T_singleton t => pfv t tag
  | T_intersection A B => pfv A tag ++ pfv B tag
  | T_union A B => pfv A tag ++ pfv B tag
  | T_top => nil
  | T_bot => nil
  | T_equal t1 t2 => pfv t1 tag ++ pfv t2 tag
  | T_forall A B => pfv A tag ++ pfv B tag
  | T_exists A B => pfv A tag ++ pfv B tag
  | T_abs T => pfv T tag
  end.

Definition fv t := pfv t term_var.
Definition tfv t := pfv t type_var.

Hint Unfold fv.
Hint Unfold tfv.

Definition tvar_list := list nat.

Definition context: Type := list (nat * tree).

Fixpoint pfv_context gamma tag :=
  match gamma with
  | nil => nil
  | (x,T) :: gamma' => x :: pfv T tag ++ pfv_context gamma' tag
  end.

Definition fv_context gamma := pfv_context gamma term_var.

Hint Unfold fv_context.

Lemma fv_context_append:
  forall gamma1 gamma2 tag,
    pfv_context (gamma1 ++ gamma2) tag = pfv_context gamma1 tag ++ pfv_context gamma2 tag.
Proof.
  induction gamma1; repeat step || rewrite app_assoc_reverse.
Qed.

Hint Rewrite fv_context_append: blistutils.

Fixpoint pfv_range (m: list (nat * tree)) tag :=
  match m with
  | nil => nil
  | (x,t) :: m' => pfv t tag ++ pfv_range m' tag
  end.

Definition fv_range (m: list (nat * tree)) := pfv_range m term_var.

Hint Unfold fv_range.

Fixpoint pclosed_mapping (m: list (nat * tree)) tag: Prop :=
  match m with
  | nil => True
  | (x,t) :: m' => pfv t tag = nil /\ pclosed_mapping m' tag
  end.

Definition closed_mapping (m: list (nat * tree)): Prop := pclosed_mapping m term_var.

Hint Unfold closed_mapping.

Fixpoint psubstitute t (l: list (nat * tree)) (tag: fv_tag): tree :=
  match t with
  | fvar x tag' =>
    match lookup Nat.eq_dec l x with
    | None => t
    | Some e =>
      if (tag_eq_dec tag tag')
      then e
      else t
    end

  | lvar _ _ => t
  | err => t

  | uu => t

  | notype_lambda t' => notype_lambda (psubstitute t' l tag)
  | lambda T t' => lambda (psubstitute T l tag) (psubstitute t' l tag)
  | app t1 t2 => app (psubstitute t1 l tag) (psubstitute t2 l tag)

  | type_abs t' => type_abs (psubstitute t' l tag)
  | type_inst t' T => type_inst (psubstitute t' l tag) (psubstitute T l tag)
  | notype_inst t'=> notype_inst (psubstitute t' l tag)

  | pp t1 t2 => pp (psubstitute t1 l tag) (psubstitute t2 l tag)
  | pi1 t' => pi1 (psubstitute t' l tag)
  | pi2 t' => pi2 (psubstitute t' l tag)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (psubstitute t1 l tag) (psubstitute t2 l tag) (psubstitute t3 l tag)

  | zero => t
  | succ t' => succ (psubstitute t' l tag)
  | notype_rec t' t1 t2 =>
      notype_rec (psubstitute t' l tag) (psubstitute t1 l tag) (psubstitute t2 l tag)
  | rec T t' t1 t2 =>
      rec (psubstitute T l tag) (psubstitute t' l tag)
          (psubstitute t1 l tag) (psubstitute t2 l tag)
  | tmatch t' t1 t2 => tmatch (psubstitute t' l tag) (psubstitute t1 l tag) (psubstitute t2 l tag)

  | tfix T t' => tfix (psubstitute T l tag) (psubstitute t' l tag)
  | notype_tfix t' => notype_tfix (psubstitute t' l tag)

  | notype_tlet t1 t2 => notype_tlet (psubstitute t1 l tag) (psubstitute t2 l tag)
  | tlet t1 T t2 => tlet (psubstitute t1 l tag) (psubstitute T l tag) (psubstitute t2 l tag)
  | trefl => t

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_arrow T1 T2 => T_arrow (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_refine T p => T_refine (psubstitute T l tag) (psubstitute p l tag)
  | T_let t A B => T_let (psubstitute t l tag) (psubstitute A l tag) (psubstitute B l tag)
  | T_singleton t => T_singleton (psubstitute t l tag)
  | T_intersection T1 T2 => T_intersection (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_union T1 T2 => T_union (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (psubstitute t1 l tag) (psubstitute t2 l tag)
  | T_forall T1 T2 => T_forall (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_exists T1 T2 => T_exists (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_abs T => T_abs (psubstitute T l tag)
  end.

Definition substitute t l := psubstitute t l term_var.
Definition substitute_type_vars t l := psubstitute t l type_var.

Hint Unfold substitute.
Hint Unfold substitute_type_vars.

Fixpoint psubstitute_context (gamma: context) (l: list (nat * tree)) tag: context :=
  match gamma with
  | nil => nil
  | (x,T) :: gamma' => (x, psubstitute T l tag) :: psubstitute_context gamma' l tag
  end.

Definition substitute_context (gamma: context) (l: list (nat * tree)): context :=
  psubstitute_context gamma l term_var.

Fixpoint open (k: nat) (t rep: tree) :=
  match t with
  | fvar _ _ => t
  | lvar i term_var => if (Nat.eq_dec k i) then rep else t
  | lvar i type_var => t
  | err => t

  | notype_lambda t' => notype_lambda (open (S k) t' rep)
  | lambda T t' => lambda (open k T rep) (open (S k) t' rep)
  | app t1 t2 => app (open k t1 rep) (open k t2 rep)

  | type_abs t => type_abs (open k t rep)
  | type_inst t T => type_inst (open k t rep) (open k T rep)
  | notype_inst t => notype_inst (open k t rep)

  | uu => t

  | pp t1 t2 => pp (open k t1 rep) (open k t2 rep)
  | pi1 t => pi1 (open k t rep)
  | pi2 t => pi2 (open k t rep)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (open k t1 rep) (open k t2 rep) (open k t3 rep)

  | zero => t
  | succ t' => succ (open k t' rep)
  | notype_rec t' t1 t2 =>
      notype_rec (open k t' rep)
                 (open k t1 rep)
                 (open (S (S k)) t2 rep)
  | rec T t' t1 t2 =>
      rec (open (S k) T rep)
          (open k t' rep)
          (open k t1 rep)
          (open (S (S k)) t2 rep)
  | tmatch t' t1 t2 =>
      tmatch
          (open k t' rep)
          (open k t1 rep)
          (open (S k) t2 rep)

  | tfix T t' => tfix (open (S k) T rep) (open (S k) t' rep)
  | notype_tfix t' => notype_tfix (open (S k) t' rep)

  | notype_tlet t1 t2 =>
      notype_tlet (open k t1 rep) (open (S k) t2 rep)
  | tlet t1 T t2 =>
      tlet (open k t1 rep) (open k T rep) (open (S k) t2 rep)
  | trefl => t

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (open k T1 rep) (open (S k) T2 rep)
  | T_arrow T1 T2 => T_arrow (open k T1 rep) (open (S k) T2 rep)
  | T_refine T p => T_refine (open k T rep) (open (S k) p rep)
  | T_let t A B => T_let (open k t rep) (open k A rep) (open (S k) B rep)
  | T_singleton t => T_singleton (open k t rep)
  | T_intersection T1 T2 => T_intersection (open k T1 rep) (open k T2 rep)
  | T_union T1 T2 => T_union (open k T1 rep) (open k T2 rep)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (open k t1 rep) (open k t2 rep)
  | T_forall T1 T2 => T_forall (open k T1 rep) (open (S k) T2 rep)
  | T_exists T1 T2 => T_exists (open k T1 rep) (open (S k) T2 rep)
  | T_abs T => T_abs (open k T rep)
  end.

Fixpoint topen (k: nat) (t rep: tree) :=
  match t with
  | fvar _ _ => t
  | lvar i type_var => if (Nat.eq_dec k i) then rep else t
  | lvar i term_var => t
  | err => t

  | notype_lambda t' => notype_lambda (topen k t' rep)
  | lambda T t' => lambda (topen k T rep) (topen k t' rep)
  | app t1 t2 => app (topen k t1 rep) (topen k t2 rep)

  | type_abs t => type_abs (topen (S k) t rep)
  | type_inst t T => type_inst (topen k t rep) (topen k T rep)
  | notype_inst t => notype_inst (topen k t rep)

  | uu => t

  | pp t1 t2 => pp (topen k t1 rep) (topen k t2 rep)
  | pi1 t => pi1 (topen k t rep)
  | pi2 t => pi2 (topen k t rep)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (topen k t1 rep) (topen k t2 rep) (topen k t3 rep)

  | zero => t
  | succ t' => succ (topen k t' rep)
  | notype_rec t' t1 t2 =>
      notype_rec (topen k t' rep)
                 (topen k t1 rep)
                 (topen k t2 rep)
  | rec T t' t1 t2 =>
      rec (topen k T rep)
          (topen k t' rep)
          (topen k t1 rep)
          (topen k t2 rep)
  | tmatch t' t1 t2 =>
      tmatch
          (topen k t' rep)
          (topen k t1 rep)
          (topen k t2 rep)

  | tfix T t' => tfix (topen k T rep) (topen k t' rep)
  | notype_tfix t' => notype_tfix (topen k t' rep)

  | notype_tlet t1 t2 =>
      notype_tlet (topen k t1 rep) (topen k t2 rep)
  | tlet t1 T t2 =>
      tlet (topen k t1 rep) (topen k T rep) (topen k t2 rep)
  | trefl => t

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (topen k T1 rep) (topen k T2 rep)
  | T_arrow T1 T2 => T_arrow (topen k T1 rep) (topen k T2 rep)
  | T_refine T p => T_refine (topen k T rep) (topen k p rep)
  | T_let t A B => T_let (topen k t rep) (topen k A rep) (topen k B rep)
  | T_singleton t => T_singleton (topen k t rep)
  | T_intersection T1 T2 => T_intersection (topen k T1 rep) (topen k T2 rep)
  | T_union T1 T2 => T_union (topen k T1 rep) (topen k T2 rep)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (topen k t1 rep) (topen k t2 rep)
  | T_forall T1 T2 => T_forall (topen k T1 rep) (topen k T2 rep)
  | T_exists T1 T2 => T_exists (topen k T1 rep) (topen k T2 rep)
  | T_abs T => T_abs (topen (S k) T rep)
  end.

Fixpoint wf t k :=
  match t with
  | fvar _ _ => True
  | lvar i term_var => i < k
  | lvar i type_var => True
  | err => True

  | uu => True

  | notype_lambda t' => wf t' (S k)
  | lambda T t' => wf T k /\ wf t' (S k)
  | app t1 t2 => wf t1 k /\ wf t2 k

  | type_abs t => wf t k
  | type_inst t T => wf t k /\ wf T k
  | notype_inst t => wf t k

  | pp t1 t2 => wf t1 k /\ wf t2 k
  | pi1 t => wf t k
  | pi2 t => wf t k

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => wf t1 k /\ wf t2 k /\ wf t3 k

  | zero => True
  | succ t' => wf t' k
  | notype_rec t' t1 t2 =>
      wf t' k /\
      wf t1 k /\
      wf t2 (S (S k))
  | rec T t' t1 t2 =>
      wf T (S k) /\
      wf t' k /\
      wf t1 k /\
      wf t2 (S (S k))
  | tmatch t' t1 t2 =>
      wf t' k /\
      wf t1 k /\
      wf t2 (S k)

  | tfix T t' => wf T (S k) /\ wf t' (S k)
  | notype_tfix t' => wf t' (S k)

  | notype_tlet t1 t2 => wf t1 k /\ wf t2 (S k)
  | tlet t1 T t2 => wf t1 k /\ wf T k /\ wf t2 (S k)
  | trefl => True

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_arrow T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_refine T p => wf T k /\ wf p (S k)
  | T_let t A B => wf t k /\ wf A k /\ wf B (S k)
  | T_singleton t => wf t k
  | T_intersection T1 T2 => wf T1 k /\ wf T2 k
  | T_union T1 T2 => wf T1 k /\ wf T2 k
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => wf t1 k /\ wf t2 k
  | T_forall T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_exists T1 T2 => wf T1 k /\ wf T2 (S k)
  | T_abs T => wf T k
  end.

Fixpoint twf t k :=
  match t with
  | fvar _ _ => True
  | lvar i type_var => i < k
  | lvar i term_var => True
  | err => True

  | uu => True

  | notype_lambda t' => twf t' k
  | lambda T t' => twf T k /\ twf t' k
  | app t1 t2 => twf t1 k /\ twf t2 k

  | type_abs t => twf t (S k)
  | type_inst t T => twf t k /\ twf T k
  | notype_inst t => twf t k

  | pp t1 t2 => twf t1 k /\ twf t2 k
  | pi1 t => twf t k
  | pi2 t => twf t k

  | ttrue => True
  | tfalse => True
  | ite t1 t2 t3 => twf t1 k /\ twf t2 k /\ twf t3 k

  | zero => True
  | succ t' => twf t' k
  | notype_rec t' t1 t2 =>
      twf t' k /\
      twf t1 k /\
      twf t2 k
  | rec T t' t1 t2 =>
      twf T k /\
      twf t' k /\
      twf t1 k /\
      twf t2 k
  | tmatch t' t1 t2 =>
      twf t' k /\
      twf t1 k /\
      twf t2 k

  | tfix T t' => twf T k /\ twf t' k
  | notype_tfix t' => twf t' k

  | notype_tlet t1 t2 => twf t1 k /\ twf t2 k
  | tlet t1 T t2 => twf t1 k /\ twf T k /\ twf t2 k
  | trefl => True

  | T_unit => True
  | T_bool => True
  | T_nat => True
  | T_prod T1 T2 => twf T1 k /\ twf T2 k
  | T_arrow T1 T2 => twf T1 k /\ twf T2 k
  | T_refine T p => twf T k /\ twf p k
  | T_let t A B => twf t k /\ twf A k /\ twf B k
  | T_singleton t => twf t k
  | T_intersection T1 T2 => twf T1 k /\ twf T2 k
  | T_union T1 T2 => twf T1 k /\ twf T2 k
  | T_top => True
  | T_bot => True
  | T_equal t1 t2 => twf t1 k /\ twf t2 k
  | T_forall T1 T2 => twf T1 k /\ twf T2 k
  | T_exists T1 T2 => twf T1 k /\ twf T2 k
  | T_abs T => twf T (S k)
  end.

Fixpoint wfs (gamma: list (nat * tree)) k :=
  match gamma with
  | nil => True
  | (x,A) :: gamma' => wf A k /\ wfs gamma' k
  end.

Fixpoint twfs (gamma: list (nat * tree)) k :=
  match gamma with
  | nil => True
  | (x,A) :: gamma' => twf A k /\ twfs gamma' k
  end.

Ltac tequality :=
  match goal with
  | |- app _ _ = app _ _ => f_equal
  | |- pp _ _ = pp _ _ => f_equal
  | |- lambda _ _ = lambda _ _ => f_equal
  | |- notype_lambda _ = notype_lambda _ => f_equal
  | |- pi1 _ = pi1 _ => f_equal
  | |- pi2 _ = pi2 _ => f_equal
  | |- succ _ = succ _ => f_equal
  | |- ite _ _ _ = ite _ _ _ => f_equal
  | |- rec _ _ _ _ = rec _ _ _ _ => f_equal
  | |- notype_rec _ _ _ = notype_rec _ _ _ => f_equal
  | |- tmatch _ _ _ = tmatch _ _ _ => f_equal
  | |- tlet _ _ _ = tlet _ _ _ => f_equal
  | |- notype_tlet _ _ = notype_tlet _ _ => f_equal
  | |- type_abs _ = type_abs _ => f_equal
  | |- type_inst _ _ = type_inst _ _ => f_equal
  | |- notype_inst _ = notype_inst _ => f_equal
  | |- tfix _ _ = tfix _ _ => f_equal
  | |- notype_tfix _ = notype_tfix _ => f_equal

  | |- T_refine _ _ = T_refine _ _ => f_equal
  | |- T_prod _ _ = T_prod _ _ => f_equal
  | |- T_arrow _ _ = T_arrow _ _ => f_equal
  | |- T_let _ _ _ = T_let _ _ _ => f_equal
  | |- T_singleton _ = T_singleton _ => f_equal
  | |- T_intersection _ _ = T_intersection _ _ => f_equal
  | |- T_union _ _ = T_union _ _ => f_equal
  | |- T_equal _ _ = T_equal _ _ => f_equal
  | |- T_forall _ _ = T_forall _ _ => f_equal
  | |- T_exists _ _ = T_exists _ _ => f_equal
  | |- T_abs _ = T_abs _ => f_equal
 end.

Lemma fold_open_arrow:
  forall T1 T2 rep,
    T_arrow (open 0 T1 rep) (open 1 T2 rep) = open 0 (T_arrow T1 T2) rep.
Proof.
  reflexivity.
Qed.

Lemma fold_open_refine:
  forall T p rep,
    T_refine (open 0 T rep) (open 1 p rep) = open 0 (T_refine T p) rep.
Proof.
  reflexivity.
Qed.

Fixpoint closed_terms (ltypes: list (nat * tree)): Prop :=
  match ltypes with
  | nil => True
  | (_, t) :: ts =>
    closed_terms ts /\
    wf t 0 /\
    twf t 0 /\
    pfv t term_var = nil /\
    pfv t type_var = nil
  end.
