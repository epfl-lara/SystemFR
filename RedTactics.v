Require Import Termination.Tactics.
Require Import Termination.Freshness.
Require Import Termination.FVLemmas.
Require Import Termination.ListUtils.
Require Import Termination.SubstitutionLemmas.
Require Import Termination.TermList.
Require Import Termination.TermListLemmas.
Require Import Termination.ReducibilityDefinition.

Ltac t_rewrite := repeat step || t_listutils || t_fv_open || finisher;
                  eauto with bwf; eauto with bfv;
                  eauto with b_cmap bfv.
Ltac tac1 :=
  repeat step || t_listutils || finisher || apply SatCons || simp_red ||
         apply satisfies_insert || t_satisfies_nodup || t_fv_open || 
         (rewrite substitute_nothing2 in * by t_rewrite) ||
         (rewrite substitute_open3 in * by t_rewrite) ||
         (rewrite substitute_skip in * by t_rewrite) ||
         (rewrite substitute_open in * by t_rewrite) ||
             eauto with b_equiv;
             eauto with bwf bfv;
             eauto 3 using NoDup_append with sets.
