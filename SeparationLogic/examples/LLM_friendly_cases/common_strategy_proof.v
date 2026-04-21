Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma common_strategy0_correctness : common_strategy0.
  pre_process_default.
Qed.

Lemma common_strategy1_correctness : common_strategy1.
  pre_process_default.
Qed.

Lemma common_strategy6_correctness : common_strategy6.
Admitted.

Lemma common_strategy3_correctness : common_strategy3.
  pre_process_default.
Qed.

Lemma common_strategy7_correctness : common_strategy7.
  pre_process_default.
Qed.

Lemma common_strategy8_correctness : common_strategy8.
Admitted.

Lemma common_strategy9_correctness : common_strategy9.
  pre_process_default.
  apply poly_store_poly_undef_store.
Qed.

Lemma common_strategy10_correctness : common_strategy10.
  pre_process_default.
Qed.

Lemma common_strategy11_correctness : common_strategy11.
Admitted.

Lemma common_strategy12_correctness : common_strategy12.
Proof.
  pre_process_default.
Qed.

Lemma common_strategy13_correctness : common_strategy13.
Proof. 
  pre_process_default.
Qed.

Lemma common_strategy14_correctness : common_strategy14.
Proof.
  pre_process_default.
  apply poly_store_poly_undef_store.
Qed.

Lemma common_strategy15_correctness : common_strategy15.
Admitted.

Lemma common_strategy16_correctness : common_strategy16.
Admitted.

Lemma common_strategy17_correctness : common_strategy17.
Admitted.

Lemma common_strategy18_correctness : common_strategy18.
Proof.
  pre_process_default.
Qed.

Lemma common_strategy19_correctness : common_strategy19.
Admitted.

Lemma common_strategy20_correctness : common_strategy20.
Admitted.

Lemma common_strategy21_correctness : common_strategy21.
Admitted.

Lemma common_strategy22_correctness : common_strategy22.
Admitted.

Lemma common_strategy23_correctness : common_strategy23.
Admitted.