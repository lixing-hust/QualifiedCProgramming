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
From SimpleC.EE.CAV.verify_20260421_020437_count_divisors Require Import count_divisors_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_divisors.
Require Import count_divisors_verify_aux.
Local Open Scope sac.

Lemma count_divisors_upto_bounds :
  forall n fuel,
    0 <= count_divisors_upto n fuel <= Z.of_nat fuel.
Proof.
  intros n fuel.
  induction fuel.
  - simpl. lia.
  - simpl.
    assert (HS: Z.pos (Pos.of_succ_nat fuel) = Z.of_nat fuel + 1).
    {
      change (Z.pos (Pos.of_succ_nat fuel)) with (Z.of_nat (S fuel)).
      rewrite Nat2Z.inj_succ.
      lia.
    }
    destruct (Z.eq_dec (Z.rem n (Z.pos (Pos.of_succ_nat fuel))) 0); lia.
Qed.

Lemma count_divisors_prefix_bounds :
  forall n limit,
    0 <= limit ->
    0 <= count_divisors_prefix n limit <= limit.
Proof.
  intros n limit Hlimit.
  unfold count_divisors_prefix.
  pose proof (count_divisors_upto_bounds n (Z.to_nat limit)).
  rewrite Z2Nat.id in H by lia.
  lia.
Qed.

Lemma count_divisors_prefix_zero :
  forall n, count_divisors_prefix n 0 = 0.
Proof.
  intros n.
  unfold count_divisors_prefix.
  simpl.
  reflexivity.
Qed.

Lemma Z_to_nat_succ_pred :
  forall d,
    1 <= d ->
    Z.to_nat d = S (Z.to_nat (d - 1)).
Proof.
  intros d Hd.
  assert (Hd_eq: d = Z.succ (d - 1)) by lia.
  rewrite Hd_eq at 1.
  rewrite Z2Nat.inj_succ by lia.
  reflexivity.
Qed.

Lemma count_divisors_prefix_step_hit :
  forall n d,
    1 <= d ->
    Z.rem n d = 0 ->
    count_divisors_prefix n d =
      count_divisors_prefix n (d - 1) + 1.
Proof.
  intros n d Hd Hrem.
  unfold count_divisors_prefix.
  replace (Z.to_nat d) with (S (Z.to_nat (d - 1))).
  2:{ symmetry. apply Z_to_nat_succ_pred. lia. }
  simpl.
  replace (Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))) with d.
  2:{
    change (Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1))))
      with (Z.of_nat (S (Z.to_nat (d - 1)))).
    replace (S (Z.to_nat (d - 1))) with (Z.to_nat d).
    - rewrite Z2Nat.id by lia. reflexivity.
    - rewrite Z_to_nat_succ_pred by lia. reflexivity.
  }
  destruct (Z.eq_dec (Z.rem n d) 0); lia.
Qed.

Lemma count_divisors_prefix_step_miss :
  forall n d,
    1 <= d ->
    Z.rem n d <> 0 ->
    count_divisors_prefix n d =
      count_divisors_prefix n (d - 1).
Proof.
  intros n d Hd Hrem.
  unfold count_divisors_prefix.
  replace (Z.to_nat d) with (S (Z.to_nat (d - 1))).
  2:{ symmetry. apply Z_to_nat_succ_pred. lia. }
  simpl.
  replace (Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))) with d.
  2:{
    change (Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1))))
      with (Z.of_nat (S (Z.to_nat (d - 1)))).
    replace (S (Z.to_nat (d - 1))) with (Z.to_nat d).
    - rewrite Z2Nat.id by lia. reflexivity.
    - rewrite Z_to_nat_succ_pred by lia. reflexivity.
  }
  destruct (Z.eq_dec (Z.rem n d) 0); lia.
Qed.

Lemma count_divisors_prefix_full :
  forall n,
    count_divisors_prefix n n = count_divisors_spec n.
Proof.
  intros n.
  unfold count_divisors_prefix, count_divisors_spec.
  reflexivity.
Qed.

Lemma proof_of_count_divisors_safety_wit_5 : count_divisors_safety_wit_5.
Proof.
  unfold count_divisors_safety_wit_5.
  intros.
  entailer!;
    pose proof (count_divisors_prefix_bounds n_pre (d - 1));
    lia.
Qed. 

Lemma proof_of_count_divisors_entail_wit_1 : count_divisors_entail_wit_1.
Proof.
  unfold count_divisors_entail_wit_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_count_divisors_entail_wit_2_1 : count_divisors_entail_wit_2_1.
Proof.
  unfold count_divisors_entail_wit_2_1.
  intros.
  entailer!.
  subst cnt.
  replace ((d + 1) - 1) with d by lia.
  assert (Hstep:
    count_divisors_prefix n_pre d =
      count_divisors_prefix n_pre (d - 1) + 1).
  {
    apply count_divisors_prefix_step_hit.
    - lia.
    - exact H.
  }
  rewrite Hstep.
  lia.
Qed. 

Lemma proof_of_count_divisors_entail_wit_2_2 : count_divisors_entail_wit_2_2.
Proof.
  unfold count_divisors_entail_wit_2_2.
  intros.
  entailer!.
  subst cnt.
  replace ((d + 1) - 1) with d by lia.
  assert (Hstep:
    count_divisors_prefix n_pre d =
      count_divisors_prefix n_pre (d - 1)).
  {
    apply count_divisors_prefix_step_miss.
    - lia.
    - exact H.
  }
  rewrite Hstep.
  reflexivity.
Qed. 

Lemma proof_of_count_divisors_entail_wit_3 : count_divisors_entail_wit_3.
Proof.
  unfold count_divisors_entail_wit_3.
  intros.
  entailer!.
  assert (d = n_pre + 1) by lia.
  subst d.
  replace (n_pre + 1 - 1) with n_pre in H2 by lia.
  rewrite H2.
  apply count_divisors_prefix_full.
Qed. 
