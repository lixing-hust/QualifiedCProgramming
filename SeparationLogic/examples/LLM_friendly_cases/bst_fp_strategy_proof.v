Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import bst_fp_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import bst_fp_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma bst_fp_strategy0_correctness : bst_fp_strategy0.
Admitted.

Lemma bst_fp_strategy1_correctness : bst_fp_strategy1.
Admitted.

Lemma bst_fp_strategy2_correctness : bst_fp_strategy2.
Admitted.