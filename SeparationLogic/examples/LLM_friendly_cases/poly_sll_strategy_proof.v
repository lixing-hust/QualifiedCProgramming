Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import poly_sll_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.LLM_friendly_cases Require Import poly_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma poly_sll_strategy1_correctness : poly_sll_strategy1.
  pre_process_default.
Qed.

Lemma poly_sll_strategy2_correctness : poly_sll_strategy2.
  pre_process_default.
Qed.

Lemma poly_sll_strategy4_correctness : poly_sll_strategy4.
Admitted.

Lemma poly_sll_strategy5_correctness : poly_sll_strategy5.
Admitted.

Lemma poly_sll_strategy16_correctness : poly_sll_strategy16.
Admitted.

Lemma poly_sll_strategy17_correctness : poly_sll_strategy17.
Admitted.

Lemma poly_sll_strategy18_correctness : poly_sll_strategy18.
Admitted.

Lemma poly_sll_strategy7_correctness : poly_sll_strategy7.
Admitted.

Lemma poly_sll_strategy10_correctness : poly_sll_strategy10.
Admitted.

Lemma poly_sll_strategy11_correctness : poly_sll_strategy11.
Admitted.

Lemma poly_sll_strategy12_correctness : poly_sll_strategy12.
Admitted.

Lemma poly_sll_strategy8_correctness : poly_sll_strategy8.
Admitted.

Lemma poly_sll_strategy9_correctness : poly_sll_strategy9.
Admitted.

Lemma poly_sll_strategy19_correctness : poly_sll_strategy19.
  pre_process_default.
Qed.