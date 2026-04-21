Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import uint_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma uint_array_strategy1_correctness : uint_array_strategy1.
Admitted.

Lemma uint_array_strategy4_correctness : uint_array_strategy4.
Admitted.

Lemma uint_array_strategy5_correctness : uint_array_strategy5.
  pre_process_default.
Qed.

Lemma uint_array_strategy6_correctness : uint_array_strategy6.
Admitted.

Lemma uint_array_strategy7_correctness : uint_array_strategy7.
Admitted.

Lemma uint_array_strategy8_correctness : uint_array_strategy8.
Admitted.

Lemma uint_array_strategy9_correctness : uint_array_strategy9.
Admitted.

Lemma uint_array_strategy10_correctness : uint_array_strategy10.
Admitted.

Lemma uint_array_strategy2_correctness : uint_array_strategy2.
Admitted.

Lemma uint_array_strategy11_correctness : uint_array_strategy11.
Admitted.

Lemma uint_array_strategy3_correctness : uint_array_strategy3.
Admitted.

Lemma uint_array_strategy12_correctness : uint_array_strategy12.
Admitted.

Lemma uint_array_strategy13_correctness : uint_array_strategy13.
Admitted.

Lemma uint_array_strategy14_correctness : uint_array_strategy14.
Admitted.
