Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import eval_strategy_goal.
Import naive_C_Rules.

From SimpleC.EE.LLM_friendly_cases Require Import eval_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma eval_strategy0_correctness : eval_strategy0.
Admitted.

Lemma eval_strategy1_correctness : eval_strategy1.
Admitted.
