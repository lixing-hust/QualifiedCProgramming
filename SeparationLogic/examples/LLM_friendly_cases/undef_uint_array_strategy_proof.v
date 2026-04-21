Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import undef_uint_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma undef_uint_array_strategy1_correctness : undef_uint_array_strategy1.
Admitted.

Lemma undef_uint_array_strategy7_correctness : undef_uint_array_strategy7.
Admitted.

Lemma undef_uint_array_strategy8_correctness : undef_uint_array_strategy8.
Admitted.

Lemma undef_uint_array_strategy9_correctness : undef_uint_array_strategy9.
  pre_process_default.
  subst.
  apply UIntArray.undef_seg_empty.
Qed.

Lemma undef_uint_array_strategy10_correctness : undef_uint_array_strategy10.
Admitted.

Lemma undef_uint_array_strategy11_correctness : undef_uint_array_strategy11.
Admitted.

Lemma undef_uint_array_strategy13_correctness : undef_uint_array_strategy13.
Admitted.

Lemma undef_uint_array_strategy2_correctness : undef_uint_array_strategy2.
Admitted.

Lemma undef_uint_array_strategy3_correctness : undef_uint_array_strategy3.
Admitted. 

Lemma undef_uint_array_strategy12_correctness : undef_uint_array_strategy12.
Admitted.

Lemma undef_uint_array_strategy14_correctness : undef_uint_array_strategy14.
Admitted.

Lemma undef_uint_array_strategy4_correctness : undef_uint_array_strategy4.
Admitted.


Lemma undef_uint_array_strategy17_correctness : undef_uint_array_strategy17.
Admitted.

Lemma undef_uint_array_strategy18_correctness : undef_uint_array_strategy18.
Admitted.

Lemma undef_uint_array_strategy19_correctness : undef_uint_array_strategy19.
  pre_process_default.
  subst.
  apply IntArray.undef_seg_empty.
Qed.

Lemma undef_uint_array_strategy20_correctness : undef_uint_array_strategy20.
Admitted.

Lemma undef_uint_array_strategy5_correctness : undef_uint_array_strategy5.
Admitted.

Lemma undef_uint_array_strategy15_correctness : undef_uint_array_strategy15.
Admitted.

Lemma undef_uint_array_strategy6_correctness : undef_uint_array_strategy6.
Admitted.

Lemma undef_uint_array_strategy16_correctness : undef_uint_array_strategy16.
Admitted.

Lemma undef_uint_array_strategy21_correctness : undef_uint_array_strategy21.
Admitted.

Lemma undef_uint_array_strategy22_correctness : undef_uint_array_strategy22.
Admitted.
