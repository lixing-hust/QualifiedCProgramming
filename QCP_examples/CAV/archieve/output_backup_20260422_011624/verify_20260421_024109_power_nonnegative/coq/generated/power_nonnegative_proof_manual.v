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
From SimpleC.EE.CAV.verify_20260421_024109_power_nonnegative Require Import power_nonnegative_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import power_nonnegative.
Local Open Scope sac.

Lemma power_nonnegative_z_succ :
  forall base e,
    0 <= e ->
    power_nonnegative_z base (e + 1) =
    power_nonnegative_z base e * base.
Proof.
  intros.
  unfold power_nonnegative_z.
  replace (e + 1) with (Z.succ e) by lia.
  rewrite Z2Nat.inj_succ by lia.
  reflexivity.
Qed.

Lemma proof_of_power_nonnegative_safety_wit_3 : power_nonnegative_safety_wit_3.
Proof.
  unfold power_nonnegative_safety_wit_3.
  pre_process.
  entailer!.
  - subst.
    rewrite <- power_nonnegative_z_succ by lia.
    pose proof (H4 (i + 1)).
    lia.
  - subst.
    rewrite <- power_nonnegative_z_succ by lia.
    pose proof (H4 (i + 1)).
    lia.
Qed.

Lemma proof_of_power_nonnegative_entail_wit_1 : power_nonnegative_entail_wit_1.
Proof.
  unfold power_nonnegative_entail_wit_1.
  pre_process.
Qed.

Lemma proof_of_power_nonnegative_entail_wit_2 : power_nonnegative_entail_wit_2.
Proof.
  unfold power_nonnegative_entail_wit_2.
  pre_process.
  entailer!.
  subst.
  rewrite power_nonnegative_z_succ by lia.
  reflexivity.
Qed.
