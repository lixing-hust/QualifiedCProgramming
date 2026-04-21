Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import safeexecE_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.LLM_friendly_cases Require Import kmp_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma safeexecE_strategy3_correctness : safeexecE_strategy3.
Admitted.

Lemma safeexecE_strategy4_correctness : safeexecE_strategy4.
  pre_process_default.
Qed.

Lemma safeexecE_strategy5_correctness : safeexecE_strategy5.
  pre_process_default.
Qed.

Lemma safeexecE_strategy1_correctness : safeexecE_strategy1.
  pre_process_default.
Qed.

Lemma safeexecE_strategy6_correctness : safeexecE_strategy6.
  pre_process_default.
Qed.

Lemma safeexecE_strategy7_correctness : safeexecE_strategy7.
  pre_process_default.
Qed.

Lemma safeexecE_strategy8_correctness : safeexecE_strategy8.
Admitted.

Lemma safeexecE_strategy9_correctness : safeexecE_strategy9.
Admitted.

Lemma safeexecE_strategy2_correctness : safeexecE_strategy2.
Admitted.
