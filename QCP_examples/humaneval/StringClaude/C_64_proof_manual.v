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
From SimpleC.EE Require Import C_64_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_64.
Local Open Scope sac.

Ltac solve_vowel_hit :=
  pre_process;
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | i : Z, l : list Z |- _ =>
      assert (Hhit:
        Znth i l 0 = 97 \/ Znth i l 0 = 101 \/ Znth i l 0 = 105 \/
        Znth i l 0 = 111 \/ Znth i l 0 = 117 \/
        Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
        Znth i l 0 = 79 \/ Znth i l 0 = 85) by lia;
      rewrite count_regular_vowels_upto_step_hit by (lia || exact Hhit)
  end;
  entailer!.

Lemma proof_of_vowels_count_entail_wit_1 : vowels_count_entail_wit_1.
Proof.
  unfold vowels_count_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite count_regular_vowels_upto_0.
  entailer!.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_1 : vowels_count_entail_wit_2_1.
Proof.
  unfold vowels_count_entail_wit_2_1.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_2 : vowels_count_entail_wit_2_2.
Proof.
  unfold vowels_count_entail_wit_2_2.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_3 : vowels_count_entail_wit_2_3.
Proof.
  unfold vowels_count_entail_wit_2_3.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_4 : vowels_count_entail_wit_2_4.
Proof.
  unfold vowels_count_entail_wit_2_4.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_5 : vowels_count_entail_wit_2_5.
Proof.
  unfold vowels_count_entail_wit_2_5.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_6 : vowels_count_entail_wit_2_6.
Proof.
  unfold vowels_count_entail_wit_2_6.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_7 : vowels_count_entail_wit_2_7.
Proof.
  unfold vowels_count_entail_wit_2_7.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_8 : vowels_count_entail_wit_2_8.
Proof.
  unfold vowels_count_entail_wit_2_8.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_9 : vowels_count_entail_wit_2_9.
Proof.
  unfold vowels_count_entail_wit_2_9.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_10 : vowels_count_entail_wit_2_10.
Proof.
  unfold vowels_count_entail_wit_2_10.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_vowels_count_entail_wit_2_11 : vowels_count_entail_wit_2_11.
Proof.
  unfold vowels_count_entail_wit_2_11.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  repeat rewrite app_Znth1 in * by lia.
  rewrite count_regular_vowels_upto_step_miss by lia.
  entailer!.
Qed.

Lemma proof_of_vowels_count_return_wit_1 : vowels_count_return_wit_1.
Proof.
  unfold vowels_count_return_wit_1.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  eapply problem_64_spec_z_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_hit with (n := len) by (auto; lia).
  lia.
Qed.

Lemma proof_of_vowels_count_return_wit_2 : vowels_count_return_wit_2.
Proof.
  unfold vowels_count_return_wit_2.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  eapply problem_64_spec_z_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_hit with (n := len) by (auto; lia).
  lia.
Qed.

Lemma proof_of_vowels_count_return_wit_3 : vowels_count_return_wit_3.
Proof.
  unfold vowels_count_return_wit_3.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  entailer!.
  eapply problem_64_spec_z_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_zero by lia.
  lia.
Qed.

Lemma proof_of_vowels_count_return_wit_4 : vowels_count_return_wit_4.
Proof.
  unfold vowels_count_return_wit_4.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  eapply problem_64_spec_z_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_miss with (n := len) by (auto; lia).
  lia.
Qed.
