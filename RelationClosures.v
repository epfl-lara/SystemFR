Require Export SystemFR.Tactics.

Inductive star {T} (R: T -> T -> Prop): T -> T -> Prop :=
| Refl: forall t,
    star R t t
| Trans: forall t1 t2 t3,
    R t1 t2 ->
    star R t2 t3 ->
    star R t1 t3.

Hint Constructors star: star.

Lemma star_one:
  forall T (R: T -> T -> Prop) t1 t2,
    R t1 t2 ->
    star R t1 t2.
Proof.
  eauto with star.
Qed.

Lemma star_trans:
  forall T (R: T -> T -> Prop) t1 t2,
    star R t1 t2 ->
    forall t3,
      star R t2 t3 ->
      star R t1 t3.
Proof.
  induction 1; eauto with star.
Qed.

Inductive sym_star {T} (R: T -> T -> Prop): T -> T -> Prop :=
| SymRefl: forall t,
    sym_star R t t
| SymTrans: forall t1 t2 t3,
    R t1 t2 ->
    sym_star R t2 t3 ->
    sym_star R t1 t3
| SymTrans': forall t1 t2 t3,
    R t2 t1 ->
    sym_star R t2 t3 ->
    sym_star R t1 t3.

Hint Constructors sym_star: sym_star.

Lemma star_sym_star:
  forall T R (t1 t2: T),
    star R t1 t2 ->
    sym_star R t1 t2.
Proof.
  induction 1; eauto with sym_star.
Qed.

Lemma sym_star_trans:
  forall T R (t1 t2 t3: T),
    sym_star R t1 t2 ->
    sym_star R t2 t3 ->
    sym_star R t1 t3.
Proof.
  intros; generalize dependent t3.
  induction H;
    repeat step; eauto with sym_star.
Qed.

Lemma sym_star_one:
  forall T (R: T -> T -> Prop) t1 t2,
    R t1 t2 ->
    sym_star R t1 t2.
Proof.
  eauto with sym_star.
Qed.

Lemma sym_star_sym:
  forall T R (t1 t2: T),
    sym_star R t1 t2 ->
    sym_star R t2 t1.
Proof.
  induction 1; intros; eauto using sym_star_one, sym_star_trans with sym_star.
Qed.
