Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_78_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_78.
Local Open Scope sac.

Ltac solve_hex_hit :=
  pre_process;
  repeat match goal with
  | H : ?x = count_prime_hex_upto ?i ?l |- _ => subst x
  end;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | i : Z, l : list Z |- _ =>
      assert (Hhit:
        Znth i l 0 = 50 \/ Znth i l 0 = 51 \/ Znth i l 0 = 53 \/
        Znth i l 0 = 55 \/ Znth i l 0 = 66 \/ Znth i l 0 = 68) by lia;
      rewrite count_prime_hex_upto_step_hit by (lia || exact Hhit)
  end;
  entailer!.

Lemma proof_of_hex_key_entail_wit_1 : hex_key_entail_wit_1.
Proof.
  unfold hex_key_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite count_prime_hex_upto_0.
  entailer!.
Qed.

Lemma proof_of_hex_key_entail_wit_2_1 : hex_key_entail_wit_2_1.
Proof.
  unfold hex_key_entail_wit_2_1.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_hex_key_entail_wit_2_2 : hex_key_entail_wit_2_2.
Proof.
  unfold hex_key_entail_wit_2_2.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_hex_key_entail_wit_2_3 : hex_key_entail_wit_2_3.
Proof.
  unfold hex_key_entail_wit_2_3.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_hex_key_entail_wit_2_4 : hex_key_entail_wit_2_4.
Proof.
  unfold hex_key_entail_wit_2_4.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_hex_key_entail_wit_2_5 : hex_key_entail_wit_2_5.
Proof.
  unfold hex_key_entail_wit_2_5.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_hex_key_entail_wit_2_6 : hex_key_entail_wit_2_6.
Proof.
  unfold hex_key_entail_wit_2_6.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_hex_key_entail_wit_2_7 : hex_key_entail_wit_2_7.
Proof.
  unfold hex_key_entail_wit_2_7.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_prime_hex_upto ?i ?l |- _ => subst x
  end.
  repeat rewrite app_Znth1 in * by lia.
  rewrite count_prime_hex_upto_step_miss by lia.
  entailer!.
Qed.

Lemma proof_of_hex_key_return_wit_1 : hex_key_return_wit_1.
Proof.
  unfold hex_key_return_wit_1.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_prime_hex_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  entailer!.
  eapply problem_78_spec_z_intro; eauto.
  rewrite H2.
  reflexivity.
Qed.
