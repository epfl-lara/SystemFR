Require Export SystemFR.Freshness.
Require Export SystemFR.FVLemmasLists.
Require Export SystemFR.WFLemmasLists.
Require Export SystemFR.SubstitutionLemmas.
Require Export SystemFR.ErasedTermLemmas.

Ltac t_rewrite :=
  repeat step || list_utils || fv_open || finisher;
    eauto with wf;
    eauto with twf;
    eauto with fv;
    eauto with b_cmap fv.

Ltac t_substitutions :=
  (autorewrite with bsubst in *) ||
  (rewrite fv_subst_different_tag by (steps; eauto with fv)) ||
  (rewrite substitute_nothing2 in * by t_rewrite) ||
  (rewrite substitute_open3 in * by t_rewrite) ||
  (rewrite substitute_topen3 in * by t_rewrite) ||
  (rewrite substitute_skip in * by t_rewrite) ||
  (rewrite substitute_open in * by t_rewrite) ||
  (rewrite substitute_topen in * by t_rewrite) ||
  (rewrite (substitute_nothing5 (build_nat _)) by auto with fv) ||
  (rewrite (substitute_nothing5 (is_pair _)) by auto with fv) ||
  (rewrite (substitute_nothing5 (is_succ _)) by auto with fv) ||
  (rewrite (substitute_nothing5 (is_lambda _)) by auto with fv).

Ltac t_closing :=
  unfold closed_value, closed_term in *; repeat step || list_utils;
    eauto 2 with erased;
    eauto 2 with wf;
    eauto 2 with twf;
    eauto 2 with fv;
    eauto 2 with values;
    eauto 2 using is_erased_term_tfv;
    eauto 2 using is_erased_term_twf.

Ltac t_closer := try solve [ t_closing ].

#[export]
Hint Extern 1 => t_closing: closing.
