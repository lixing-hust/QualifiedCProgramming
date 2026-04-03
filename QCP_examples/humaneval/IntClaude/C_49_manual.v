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
From SimpleC.EE Require Import C_49_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_49.
Local Open Scope sac.

(* Division safety: p_pre >= 2, so p_pre <> 0 and p_pre <> -1 *)
Lemma proof_of_modp_safety_wit_4 : modp_safety_wit_4.
Proof.
  unfold modp_safety_wit_4.
  intros.
  Intros.
  entailer!.
Qed.

(* Overflow safety: out = 2^i % p_pre < p_pre, and p_pre * 2 <= INT_MAX,
   so out * 2 < p_pre * 2 <= INT_MAX, and out >= 0 so out * 2 >= 0 > INT_MIN *)
Lemma proof_of_modp_safety_wit_5 : modp_safety_wit_5.
Proof.
  unfold modp_safety_wit_5.
  intros.
  Intros.
  entailer!.
  (* After entailer!, out has been substituted with 2^i % p_pre *)
  pose proof (Z.mod_pos_bound (2^i) p_pre ltac:(lia)) as [Hmod_nn Hmod_lt].
  nia.
Qed.

Lemma proof_of_modp_entail_wit_1 : modp_entail_wit_1.
Proof.
  unfold modp_entail_wit_1.
  intros.
  Intros.
  entailer!.
  rewrite Z.pow_0_r.
  rewrite Z.mod_1_l by lia.
  reflexivity.
Qed.

Lemma proof_of_modp_entail_wit_2 : modp_entail_wit_2.
Proof.
  unfold modp_entail_wit_2.
  intros.
  Intros.
  entailer!.
  subst.
  rewrite Z.pow_succ_r by lia.
  rewrite <- Z.mul_mod_idemp_l.
  ring_simplify.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

Lemma proof_of_modp_return_wit_1 : modp_return_wit_1.
Proof.
  unfold modp_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold problem_49_spec.
  intro Hpre.
  assert (i = n_pre) by lia.
  subst.
  assumption.
Qed.
