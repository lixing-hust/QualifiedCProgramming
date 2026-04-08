Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_31_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_31.
Local Open Scope sac.

Lemma proof_of_is_prime_safety_wit_4 : is_prime_safety_wit_4.
Proof.
  unfold is_prime_safety_wit_4.
  intros.
  Intros.
  entailer!.
Qed. 

Lemma proof_of_is_prime_entail_wit_2 : is_prime_entail_wit_2.
Proof.
  unfold is_prime_entail_wit_2.
  intros.
  Intros.
  entailer!.
  - intros k Hk.
    destruct Hk as [Hk_ge2 Hk_lt_i1].
    assert (k < i \/ k = i) as Hcase by nia.
    destruct Hcase as [Hk_lt_i | Hk_eq_i].
    + apply H4; nia.
    + subst k.
      exact H.
  - assert (Hi_lt : i < 46340).
    {
      destruct (Z.eq_dec i 46340) as [Hi_eq | Hi_neq].
      + subst i.
        assert (Hn_eq : n_pre = 2147395600) by nia.
        subst n_pre.
        vm_compute in H.
        contradiction.
      + nia.
    }
    nia.
Qed. 

Lemma proof_of_is_prime_return_wit_1 : is_prime_return_wit_1.
Proof.
  unfold is_prime_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold problem_31_spec_z, IsPrime.
  assert (Hcases : n_pre = 0 \/ n_pre = 1) by nia.
  destruct Hcases as [-> | ->]; split; intro Hc.
  - contradiction.
  - destruct Hc as [Hlt _]. lia.
  - contradiction.
  - destruct Hc as [Hlt _]. lia.
Qed. 

Lemma proof_of_is_prime_return_wit_2 : is_prime_return_wit_2.
Proof.
  unfold is_prime_return_wit_2.
  intros.
  Intros.
  entailer!.
  unfold problem_31_spec_z, IsPrime.
  split.
  - intro Hc. contradiction.
  - intro Hprime.
    destruct Hprime as [Hgt1 Hprime].
    assert (Hi_nonneg : 0 <= i) by nia.
    assert (Hn_nonneg : 0 <= n_pre) by nia.
    assert (Hi_nz : i <> 0) by lia.
    pose proof (proj1 (Z.rem_divide n_pre i Hi_nz) H) as Hdiv.
    destruct Hdiv as [q Hdiv_eq].
    assert (Hq_nonneg : 0 <= q) by nia.
    assert (Hnat_eq : Z.to_nat n_pre = (Z.to_nat i * Z.to_nat q)%nat).
    {
      pose proof (f_equal Z.to_nat Hdiv_eq) as Htmp.
      rewrite Z2Nat.inj_mul in Htmp by lia.
      rewrite Nat.mul_comm in Htmp.
      exact Htmp.
    }
    assert (Hnat_mod : (Z.to_nat n_pre mod Z.to_nat i)%nat = 0%nat).
    {
      rewrite Hnat_eq.
      rewrite Nat.mul_comm.
      apply Nat.Div0.mod_mul.
    }
    specialize (Hprime (Z.to_nat i) Hnat_mod).
    assert (Hi_ne_1 : (Z.to_nat i <> 1)%nat).
    {
      intro Hi_eq.
      apply (f_equal Z.of_nat) in Hi_eq.
      rewrite Z2Nat.id in Hi_eq by nia.
      lia.
    }
    assert (Hi_lt_n : i < n_pre) by nia.
    assert (Hi_ne_n : Z.to_nat i <> Z.to_nat n_pre).
    {
      intro Heq.
      apply (f_equal Z.of_nat) in Heq.
      rewrite !Z2Nat.id in Heq by nia.
      lia.
    }
    destruct Hprime as [Hone | Hn].
    + contradiction.
    + contradiction.
Qed. 

Lemma proof_of_is_prime_return_wit_3 : is_prime_return_wit_3.
Proof.
  unfold is_prime_return_wit_3.
  intros.
  Intros.
  entailer!.
  unfold problem_31_spec_z, IsPrime.
  split.
  - intro Hnz.
    split.
    + change (Z.to_nat 1 < Z.to_nat n_pre)%nat.
      apply Z2Nat.inj_lt; nia.
    + intros d Hdmod.
      destruct d.
      * simpl in Hdmod.
        assert ((0 < Z.to_nat n_pre)%nat).
        { change (Z.to_nat 0 < Z.to_nat n_pre)%nat.
          apply Z2Nat.inj_lt; nia. }
        lia.
      * destruct d.
        { left; reflexivity. }
        { assert (Hd_ge_2 : 2 <= Z.of_nat (S (S d))) by lia.
          assert (Hn_gt1_nat : (1 < Z.to_nat n_pre)%nat).
          { change (Z.to_nat 1 < Z.to_nat n_pre)%nat.
            apply Z2Nat.inj_lt; nia. }
          destruct (lt_eq_lt_dec (S (S d)) (Z.to_nat n_pre)) as [[Hd_lt | Hd_eq] | Hd_gt].
          - assert (Hd_divides : exists c : nat, Z.to_nat n_pre = ((S (S d)) * c)%nat).
            {
              apply (proj1 (Nat.Div0.mod_divides _ _)).
              exact Hdmod.
            }
            destruct Hd_divides as [c Hnat_eq].
            assert (Hc_ge_2 : (2 <= c)%nat).
            {
              destruct c.
              - simpl in Hnat_eq. lia.
              - destruct c.
                + simpl in Hnat_eq. lia.
                + lia.
            }
            assert (Hfac : n_pre = Z.of_nat (S (S d)) * Z.of_nat c).
            {
              pose proof (f_equal Z.of_nat Hnat_eq) as Hz_eq.
              rewrite Nat2Z.inj_mul in Hz_eq.
              rewrite Z2Nat.id in Hz_eq by nia.
              exact Hz_eq.
            }
            assert (Hsmall : Z.of_nat (S (S d)) < i \/ Z.of_nat c < i) by nia.
            destruct Hsmall as [Hd_lt_i | Hc_lt_i].
            + exfalso.
              specialize (H3 (Z.of_nat (S (S d)))).
              assert (Hrange : 2 <= Z.of_nat (S (S d)) < i) by nia.
              specialize (H3 Hrange).
              apply H3.
              rewrite Hfac.
              assert (Hd_nz : Z.of_nat (S (S d)) <> 0) by lia.
              apply (proj2 (Z.rem_divide _ _ Hd_nz)).
              exists (Z.of_nat c).
              rewrite Z.mul_comm.
              reflexivity.
            + exfalso.
              specialize (H3 (Z.of_nat c)).
              assert (Hrange : 2 <= Z.of_nat c < i) by nia.
              specialize (H3 Hrange).
              apply H3.
              rewrite Hfac.
              assert (Hc_nz : Z.of_nat c <> 0) by lia.
              apply (proj2 (Z.rem_divide _ _ Hc_nz)).
              exists (Z.of_nat (S (S d))).
              reflexivity.
          - right.
            exact Hd_eq.
          - exfalso.
            rewrite Nat.mod_small in Hdmod by lia.
            assert ((0 < Z.to_nat n_pre)%nat).
            { change (Z.to_nat 0 < Z.to_nat n_pre)%nat.
              apply Z2Nat.inj_lt; nia. }
            lia. }
  - intro Hprime.
    discriminate.
Qed. 
