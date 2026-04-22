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
From SimpleC.EE.CAV.verify_20260421_034752_fibonacci_mod Require Import fibonacci_mod_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import fibonacci_mod.
Local Open Scope sac.

Lemma fib_mod_z_0_local: forall m, fib_mod_z 0 m = 0.
Proof.
  intros.
  unfold fib_mod_z, fib_mod_nat.
  simpl.
  reflexivity.
Qed.

Lemma fib_mod_z_1_local: forall m, fib_mod_z 1 m = Z.rem 1 m.
Proof.
  intros.
  unfold fib_mod_z, fib_mod_nat.
  simpl.
  reflexivity.
Qed.

Lemma fib_mod_z_step_local:
  forall k m,
    0 <= k ->
    fib_mod_z (k + 2) m = Z.rem (fib_mod_z k m + fib_mod_z (k + 1) m) m.
Proof.
  intros.
  unfold fib_mod_z, fib_mod_nat.
  replace (Z.to_nat (k + 2)) with (S (S (Z.to_nat k))).
  2: {
    rewrite Z2Nat.inj_add by lia.
    simpl.
    lia.
  }
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)).
  2: {
    rewrite Z2Nat.inj_add by lia.
    simpl.
    lia.
  }
  simpl.
  destruct (fib_mod_pair (Z.to_nat k) m).
  simpl.
  reflexivity.
Qed.

Lemma proof_of_fibonacci_mod_entail_wit_1 : fibonacci_mod_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - apply Z.rem_bound_pos; lia.
  - apply Z.rem_nonneg; lia.
Qed.

Lemma proof_of_fibonacci_mod_entail_wit_2 : fibonacci_mod_entail_wit_2.
Proof.
  pre_process.
  sep_apply store_int_undef_store_int.
  entailer!.
  - replace (i + 1 - 1) with ((i - 2) + 2) by lia.
    rewrite fib_mod_z_step_local by lia.
    replace (i - 2 + 1) with (i - 1) by lia.
    rewrite <- H6.
    rewrite <- H7.
    reflexivity.
  - replace (i + 1 - 2) with (i - 1) by lia.
    assumption.
  - apply Z.rem_bound_pos; lia.
  - apply Z.rem_nonneg; lia.
Qed.

Lemma proof_of_fibonacci_mod_return_wit_1 : fibonacci_mod_return_wit_1.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  rewrite fib_mod_z_0_local.
  reflexivity.
Qed.
