Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_39_goal.
From SimpleC.EE Require Import C_39_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_39.
Local Open Scope sac.

Lemma proof_of_prime_fib_safety_wit_4 : prime_fib_safety_wit_4.
Proof.
  right. intros. entailer!.
  - pose proof (pf_loop_sum_safe count f1 f2 PreH9 ltac:(lia)).
    lia.
  - pose proof (pf_loop_sum_safe count f1 f2 PreH9 ltac:(lia)).
    lia.
Qed.

Lemma proof_of_prime_fib_entail_wit_1 : prime_fib_entail_wit_1.
Proof.
  right. intros. entailer!.
  apply pf_initial_state.
Qed.

Lemma proof_of_prime_fib_entail_wit_2 : prime_fib_entail_wit_2.
Proof.
  right. intros. entailer!.
  - apply pf_advance_from_loop; lia || exact PreH9.
  - assert (Hadv : pf_after_advance_z count f2 (f1 + f2)).
    { apply pf_advance_from_loop; lia || exact PreH9. }
    pose proof (pf_after_advance_bounds count f2 (f1 + f2) Hadv) as [[Hlo Hhi] Hsum].
    lia.
  - assert (Hadv : pf_after_advance_z count f2 (f1 + f2)).
    { apply pf_advance_from_loop; lia || exact PreH9. }
    pose proof (pf_after_advance_bounds count f2 (f1 + f2) Hadv) as [[Hlo Hhi] Hsum].
    lia.
  - assert (Hadv : pf_after_advance_z count f2 (f1 + f2)).
    { apply pf_advance_from_loop; lia || exact PreH9. }
    pose proof (pf_after_advance_bounds count f2 (f1 + f2) Hadv) as [[Hlo Hhi] Hsum].
    lia.
Qed.

Lemma proof_of_prime_fib_entail_wit_3 : prime_fib_entail_wit_3.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  apply pf_scan_start. lia.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_1 : prime_fib_entail_wit_4_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  intros _.
  apply (pf_divisor_not_finite count f1 f2 w); try assumption; try lia.
  rewrite <- Z.quot_div_nonneg by lia. exact PreH3.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_2 : prime_fib_entail_wit_4_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  intros _.
  apply (pf_divisor_not_finite count f1 f2 w); try assumption; try lia.
  rewrite <- Z.quot_div_nonneg by lia. exact PreH3.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_3 : prime_fib_entail_wit_4_3.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  intros _.
  subst isprime.
  apply (pf_scan_exit_prime count f1 f2 w).
  - assumption.
  - lia.
  - lia.
  - assumption.
  - left; lia.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_4 : prime_fib_entail_wit_4_4.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  intros Hiszero.
  unfold prime_scan_state_z in PreH17.
  destruct PreH17 as [_ [_ Hfound]].
  apply (pf_found_not_finite count f1 f2 w); try assumption; try lia.
  apply Hfound. exact Hiszero.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_5 : prime_fib_entail_wit_4_5.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  intros Hiszero.
  unfold prime_scan_state_z in PreH16.
  destruct PreH16 as [_ [_ Hfound]].
  apply (pf_found_not_finite count f1 f2 w); try assumption; try lia.
  apply Hfound. exact Hiszero.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_6 : prime_fib_entail_wit_4_6.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  intros _.
  subst isprime.
  apply (pf_scan_exit_prime count f1 f2 w).
  - assumption.
  - lia.
  - lia.
  - assumption.
  - right. rewrite <- Z.quot_div_nonneg by lia. exact PreH1.
Qed.

Lemma proof_of_prime_fib_entail_wit_5_1 : prime_fib_entail_wit_5_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  subst isprime.
  apply pf_scan_next_found. exact PreH18.
Qed.

Lemma proof_of_prime_fib_entail_wit_5_2 : prime_fib_entail_wit_5_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  subst isprime.
  apply (pf_scan_next_prime count f1 f2 w).
  - exact PreH11.
  - exact PreH18.
  - exact PreH1.
  - rewrite <- Z.quot_div_nonneg by lia. exact PreH3.
Qed.

Lemma proof_of_prime_fib_entail_wit_8_1 : prime_fib_entail_wit_8_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  - apply pf_nonprime_step.
    + exact PreH8.
    + apply PreH16. exact PreH14.
Qed.

Lemma proof_of_prime_fib_entail_wit_8_2 : prime_fib_entail_wit_8_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  - apply pf_prime_step.
    + exact PreH8.
    + apply PreH15. exact PreH17.
Qed.

Lemma proof_of_prime_fib_return_wit_1 : prime_fib_return_wit_1.
Proof.
  right. intros. entailer!.
  assert (count = n_pre) by lia. subst count.
  apply pf_loop_state_spec with (f2 := f2); auto.
Qed.

Lemma proof_of_prime_fib_return_wit_2 : prime_fib_return_wit_2.
Proof.
  right. intros. entailer!.
  subst count.
  apply pf_loop_state_spec with (f2 := f2); auto.
Qed.

Lemma proof_of_prime_fib_return_wit_3 : prime_fib_return_wit_3.
Proof.
  right. intros. entailer!.
  subst count.
  apply pf_loop_state_spec with (f2 := f2); auto.
Qed.
