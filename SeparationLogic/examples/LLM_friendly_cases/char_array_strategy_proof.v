Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import char_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma char_array_strategy1_correctness : char_array_strategy1.
Admitted.

Lemma char_array_strategy4_correctness : char_array_strategy4.
Admitted.

Lemma char_array_strategy5_correctness : char_array_strategy5.
  pre_process_default.
Qed.

Lemma char_array_strategy6_correctness : char_array_strategy6.
Admitted.

Lemma char_array_strategy2_correctness : char_array_strategy2.
Admitted.

Lemma char_array_strategy3_correctness : char_array_strategy3.
Admitted.

Lemma char_array_strategy7_correctness : char_array_strategy7.
Admitted.

Lemma char_array_strategy8_correctness : char_array_strategy8.
Admitted.

Lemma char_array_strategy9_correctness : char_array_strategy9.
Admitted.

Lemma char_array_strategy10_correctness : char_array_strategy10.
Admitted.

Lemma char_array_strategy11_correctness : char_array_strategy11.
Admitted.