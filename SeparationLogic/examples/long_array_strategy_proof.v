Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import long_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Require Import Coq.micromega.Lia.

Lemma long_array_strategy1_correctness : long_array_strategy1.
Admitted.

Lemma long_array_strategy2_correctness : long_array_strategy2.
Admitted.

Lemma long_array_strategy3_correctness : long_array_strategy3.
Admitted.

Lemma long_array_strategy4_correctness : long_array_strategy4.
Admitted.

Lemma long_array_strategy5_correctness : long_array_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma long_array_strategy6_correctness : long_array_strategy6.
Admitted.

Lemma long_array_strategy7_correctness : long_array_strategy7.
Admitted.

Lemma long_array_strategy8_correctness : long_array_strategy8.
Admitted.

Lemma long_array_strategy9_correctness : long_array_strategy9.
Admitted.

Lemma long_array_strategy10_correctness : long_array_strategy10.
Admitted.

Lemma long_array_strategy11_correctness : long_array_strategy11.
Admitted.

Lemma long_array_strategy12_correctness : long_array_strategy12.
Admitted.
