Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260421_015041_gcd_iterative Require Import gcd_iterative_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import gcd_iterative.
Local Open Scope sac.

Lemma proof_of_gcd_iterative_entail_wit_1 : gcd_iterative_entail_wit_1.
Proof.
  pre_process.
  Exists (Z.gcd a_pre b_pre).
  unfold gcd_iterative_spec.
  entailer!.
Qed.

Lemma proof_of_gcd_iterative_entail_wit_2 : gcd_iterative_entail_wit_2.
Proof.
  pre_process.
  Exists g_2.
  unfold gcd_iterative_spec in *.
  subst g_2.
  assert (Hrem_mod : a % (b) = a mod b).
  {
    apply Z.rem_mod_nonneg; lia.
  }
  assert (Hgcd_step : Z.gcd a_pre b_pre = Z.gcd b (a % (b))).
  {
    rewrite Hrem_mod.
    rewrite H4.
    replace (Z.gcd a b) with (Z.gcd b a) by apply Z.gcd_comm.
    rewrite <- (Z.gcd_mod a b) by lia.
    apply Z.gcd_comm.
  }
  assert (Hmod_nonneg : 0 <= a % (b)).
  {
    rewrite Hrem_mod.
    apply Z.mod_pos_bound; lia.
  }
  sep_apply store_int_undef_store_int.
  entailer!.
Qed.

Lemma proof_of_gcd_iterative_return_wit_1 : gcd_iterative_return_wit_1.
Proof.
  pre_process.
  unfold gcd_iterative_spec in *.
  subst b.
  rewrite Z.gcd_0_r in H4.
  rewrite Z.abs_eq in H4 by lia.
  assert (Hret : a = Z.gcd a_pre b_pre) by lia.
  entailer!.
Qed.
