Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import PeanoNat.

Require Import SystemFR.ListUtils.
Require Import SystemFR.AssocList.
Require Import SystemFR.Tactics.
Require Export SystemFR.Trees.
Require Import SystemFR.Sets.

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
  | notype_trefl => nil
  | trefl t1 t2 => pfv t1 tag ++ pfv t2 tag

  | notype_tfold t' => pfv t' tag
  | tfold T t' => pfv T tag ++ pfv t' tag
  | tunfold t' => pfv t' tag
  | tunfold_in t1 t2 => pfv t1 tag ++ pfv t2 tag

  | tleft t' => pfv t' tag
  | tright t' => pfv t' tag
  | sum_match t' tl tr => pfv t' tag ++ pfv tl tag ++ pfv tr tag

  | T_unit => nil
  | T_bool => nil
  | T_nat => nil
  | T_refine A p => pfv A tag ++ pfv p tag
  | T_prod A B => pfv A tag ++ pfv B tag
  | T_arrow A B => pfv A tag ++ pfv B tag
  | T_sum A B => pfv A tag ++ pfv B tag
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
  | T_rec n T0 Ts => pfv n tag ++ pfv T0 tag ++ pfv Ts tag
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
  | notype_trefl => notype_trefl
  | trefl t1 t2 => trefl (psubstitute t1 l tag) (psubstitute t2 l tag)

  | notype_tfold t' => notype_tfold (psubstitute t' l tag)
  | tfold T t' => tfold (psubstitute T l tag) (psubstitute t' l tag)
  | tunfold t' => tunfold (psubstitute t' l tag)
  | tunfold_in t1 t2 => tunfold_in (psubstitute t1 l tag) (psubstitute t2 l tag)

  | tleft t' => tleft (psubstitute t' l tag)
  | tright t' => tright (psubstitute t' l tag)
  | sum_match t' tl tr => sum_match (psubstitute t' l tag) (psubstitute tl l tag) (psubstitute tr l tag)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_arrow T1 T2 => T_arrow (psubstitute T1 l tag) (psubstitute T2 l tag)
  | T_sum T1 T2 => T_sum (psubstitute T1 l tag) (psubstitute T2 l tag)
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
  | T_rec n T0 Ts => T_rec (psubstitute n l tag) (psubstitute T0 l tag) (psubstitute Ts l tag)
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
  | notype_err => t
  | err T => err (open k T rep)

  | notype_lambda t' => notype_lambda (open (S k) t' rep)
  | lambda T t' => lambda (open k T rep) (open (S k) t' rep)
  | app t1 t2 => app (open k t1 rep) (open k t2 rep)

  | forall_inst t1 t2 => forall_inst (open k t1 rep) (open k t2 rep)

  | type_abs t => type_abs (open k t rep)
  | type_inst t T => type_inst (open k t rep) (open k T rep)
  | notype_inst t => notype_inst (open k t rep)

  | uu => t

  | tsize t => tsize (open k t rep)

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

  | tfix T t' => tfix (open (S k) T rep) (open (S (S k)) t' rep)
  | notype_tfix t' => notype_tfix (open (S (S k)) t' rep)

  | notype_tlet t1 t2 =>
      notype_tlet (open k t1 rep) (open (S k) t2 rep)
  | tlet t1 T t2 =>
      tlet (open k t1 rep) (open k T rep) (open (S k) t2 rep)
  | notype_trefl => t
  | trefl t1 t2 => trefl (open k t1 rep) (open k t2 rep)

  | notype_tfold t' => notype_tfold (open k t' rep)
  | tfold T t' => tfold (open k T rep) (open k t' rep)
  | tunfold t' => tunfold (open k t' rep)
  | tunfold_in t1 t2 => tunfold_in (open k t1 rep) (open (S k) t2 rep)

  | tleft t' => tleft (open k t' rep)
  | tright t' => tright (open k t' rep)
  | sum_match t' tl tr => sum_match (open k t' rep) (open (S k) tl rep) (open (S k) tr rep)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (open k T1 rep) (open (S k) T2 rep)
  | T_arrow T1 T2 => T_arrow (open k T1 rep) (open (S k) T2 rep)
  | T_sum T1 T2 => T_sum (open k T1 rep) (open k T2 rep)
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
  | T_rec n T0 Ts => T_rec (open k n rep) (open k T0 rep) (open k Ts rep)
  end.

Fixpoint close (k: nat) (t: tree) (x: nat) :=
  match t with
  | fvar y term_var => if (Nat.eq_dec x y) then lvar k term_var else t
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
  | notype_inst t => notype_inst (close k t x)

  | uu => t

  | tsize t => tsize (close k t x)

  | pp t1 t2 => pp (close k t1 x) (close k t2 x)
  | pi1 t => pi1 (close k t x)
  | pi2 t => pi2 (close k t x)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (close k t1 x) (close k t2 x) (close k t3 x)

  | zero => t
  | succ t' => succ (close k t' x)
  | notype_rec t' t1 t2 =>
      notype_rec (close k t' x)
                 (close k t1 x)
                 (close (S (S k)) t2 x)
  | rec T t' t1 t2 =>
      rec (close (S k) T x)
          (close k t' x)
          (close k t1 x)
          (close (S (S k)) t2 x)
  | tmatch t' t1 t2 =>
      tmatch
          (close k t' x)
          (close k t1 x)
          (close (S k) t2 x)

  | tfix T t' => tfix (close (S k) T x) (close (S (S k)) t' x)
  | notype_tfix t' => notype_tfix (close (S (S k)) t' x)

  | notype_tlet t1 t2 =>
      notype_tlet (close k t1 x) (close (S k) t2 x)
  | tlet t1 T t2 =>
      tlet (close k t1 x) (close k T x) (close (S k) t2 x)
  | notype_trefl => t
  | trefl t1 t2 => trefl (close k t1 x) (close k t2 x)

  | notype_tfold t' => notype_tfold (close k t' x)
  | tfold T t' => tfold (close k T x) (close k t' x)
  | tunfold t' => tunfold (close k t' x)
  | tunfold_in t1 t2 => tunfold_in (close k t1 x) (close (S k) t2 x)

  | tleft t' => tleft (close k t' x)
  | tright t' => tright (close k t' x)
  | sum_match t' tl tr => sum_match (close k t' x) (close (S k) tl x) (close (S k) tr x)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (close k T1 x) (close (S k) T2 x)
  | T_arrow T1 T2 => T_arrow (close k T1 x) (close (S k) T2 x)
  | T_sum T1 T2 => T_sum (close k T1 x) (close k T2 x)
  | T_refine T p => T_refine (close k T x) (close (S k) p x)
  | T_let t A B => T_let (close k t x) (close k A x) (close (S k) B x)
  | T_singleton t => T_singleton (close k t x)
  | T_intersection T1 T2 => T_intersection (close k T1 x) (close k T2 x)
  | T_union T1 T2 => T_union (close k T1 x) (close k T2 x)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (close k t1 x) (close k t2 x)
  | T_forall T1 T2 => T_forall (close k T1 x) (close (S k) T2 x)
  | T_exists T1 T2 => T_exists (close k T1 x) (close (S k) T2 x)
  | T_abs T => T_abs (close k T x)
  | T_rec n T0 Ts => T_rec (close k n x) (close k T0 x) (close k Ts x)
  end.

Fixpoint topen (k: nat) (t rep: tree) :=
  match t with
  | fvar _ _ => t
  | lvar i type_var => if (Nat.eq_dec k i) then rep else t
  | lvar i term_var => t

  | notype_err => t
  | err T => err (topen k T rep)

  | notype_lambda t' => notype_lambda (topen k t' rep)
  | lambda T t' => lambda (topen k T rep) (topen k t' rep)
  | app t1 t2 => app (topen k t1 rep) (topen k t2 rep)

  | forall_inst t1 t2 => forall_inst (topen k t1 rep) (topen k t2 rep)

  | type_abs t => type_abs (topen (S k) t rep)
  | type_inst t T => type_inst (topen k t rep) (topen k T rep)
  | notype_inst t => notype_inst (topen k t rep)

  | uu => t

  | tsize t => tsize (topen k t rep)

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

  | notype_trefl => t
  | trefl t1 t2 => trefl (topen k t1 rep) (topen k t2 rep)

  | notype_tfold t => notype_tfold (topen k t rep)
  | tfold T t => tfold (topen k T rep) (topen k t rep)
  | tunfold t => tunfold (topen k t rep)
  | tunfold_in t1 t2 => tunfold_in (topen k t1 rep) (topen k t2 rep)

  | tleft t' => tleft (topen k t' rep)
  | tright t' => tright (topen k t' rep)
  | sum_match t' tl tr => sum_match (topen k t' rep) (topen k tl rep) (topen k tr rep)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (topen k T1 rep) (topen k T2 rep)
  | T_arrow T1 T2 => T_arrow (topen k T1 rep) (topen k T2 rep)
  | T_sum T1 T2 => T_sum (topen k T1 rep) (topen k T2 rep)
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
  | T_rec n T0 Ts => T_rec (topen k n rep) (topen k T0 rep) (topen (S k) Ts rep)
  end.

Fixpoint tclose (k: nat) (t: tree) (x: nat) :=
  match t with
  | fvar _ term_var => t
  | fvar y type_var => if (Nat.eq_dec y x) then lvar k type_var else t
  | lvar i _ => t

  | err T => err (tclose k T x)
  | notype_err => t

  | notype_lambda t' => notype_lambda (tclose k t' x)
  | lambda T t' => lambda (tclose k T x) (tclose k t' x)
  | app t1 t2 => app (tclose k t1 x) (tclose k t2 x)

  | forall_inst t1 t2 => forall_inst (tclose k t1 x) (tclose k t2 x)

  | type_abs t => type_abs (tclose (S k) t x)
  | type_inst t T => type_inst (tclose k t x) (tclose k T x)
  | notype_inst t => notype_inst (tclose k t x)

  | uu => t

  | tsize t => tsize (tclose k t x)

  | pp t1 t2 => pp (tclose k t1 x) (tclose k t2 x)
  | pi1 t => pi1 (tclose k t x)
  | pi2 t => pi2 (tclose k t x)

  | ttrue => t
  | tfalse => t
  | ite t1 t2 t3 => ite (tclose k t1 x) (tclose k t2 x) (tclose k t3 x)

  | zero => t
  | succ t' => succ (tclose k t' x)
  | notype_rec t' t1 t2 =>
      notype_rec (tclose k t' x)
                 (tclose k t1 x)
                 (tclose k t2 x)
  | rec T t' t1 t2 =>
      rec (tclose k T x)
          (tclose k t' x)
          (tclose k t1 x)
          (tclose k t2 x)
  | tmatch t' t1 t2 =>
      tmatch
          (tclose k t' x)
          (tclose k t1 x)
          (tclose k t2 x)

  | tfix T t' => tfix (tclose k T x) (tclose k t' x)
  | notype_tfix t' => notype_tfix (tclose k t' x)

  | notype_tlet t1 t2 =>
      notype_tlet (tclose k t1 x) (tclose k t2 x)
  | tlet t1 T t2 =>
      tlet (tclose k t1 x) (tclose k T x) (tclose k t2 x)
  | notype_trefl => t
  | trefl t1 t2 => trefl (tclose k t1 x) (tclose k t2 x)

  | notype_tfold t => notype_tfold (tclose k t x)
  | tfold T t => tfold (tclose k T x) (tclose k t x)
  | tunfold t => tunfold (tclose k t x)
  | tunfold_in t1 t2 => tunfold_in (tclose k t1 x) (tclose k t2 x)

  | tleft t' => tleft (tclose k t' x)
  | tright t' => tright (tclose k t' x)
  | sum_match t' tl tr => sum_match (tclose k t' x) (tclose k tl x) (tclose k tr x)

  | T_unit => t
  | T_bool => t
  | T_nat => t
  | T_prod T1 T2 => T_prod (tclose k T1 x) (tclose k T2 x)
  | T_arrow T1 T2 => T_arrow (tclose k T1 x) (tclose k T2 x)
  | T_sum T1 T2 => T_sum (tclose k T1 x) (tclose k T2 x)
  | T_refine T p => T_refine (tclose k T x) (tclose k p x)
  | T_let t A B => T_let (tclose k t x) (tclose k A x) (tclose k B x)
  | T_singleton t => T_singleton (tclose k t x)
  | T_intersection T1 T2 => T_intersection (tclose k T1 x) (tclose k T2 x)
  | T_union T1 T2 => T_union (tclose k T1 x) (tclose k T2 x)
  | T_top => t
  | T_bot => t
  | T_equal t1 t2 => T_equal (tclose k t1 x) (tclose k t2 x)
  | T_forall T1 T2 => T_forall (tclose k T1 x) (tclose k T2 x)
  | T_exists T1 T2 => T_exists (tclose k T1 x) (tclose k T2 x)
  | T_abs T => T_abs (tclose (S k) T x)
  | T_rec n T0 Ts => T_rec (tclose k n x) (tclose k T0 x) (tclose (S k) Ts x)
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
