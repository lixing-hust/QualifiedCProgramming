Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import sll_queue_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import sll_lib.
From SimpleC.EE.LLM_friendly_cases Require Import sll_queue_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_queue_strategy0_correctness : sll_queue_strategy0.
Admitted.

Lemma sll_queue_strategy1_correctness : sll_queue_strategy1.
Admitted.
