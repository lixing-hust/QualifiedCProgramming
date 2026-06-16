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
From SimpleC.EE.QCP_demos_LLM Require Import max_sub_array_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.max_sub_array_lib.
Local Open Scope sac.

Lemma proof_of_max_return_wit_1 : max_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold max_Z.
    symmetry.
    apply Z.max_l.
    lia.
Qed.

Lemma proof_of_max_return_wit_2 : max_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold max_Z.
    symmetry.
    apply Z.max_r.
    lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2.
Proof.
  pre_process.
  assert (Hoverflow : INT_MIN <= cur + Znth i l 0 <= INT_MAX).
  {
    subst cur.
    match goal with
    | Hsafe : kadane_safe l |- _ =>
        unfold kadane_safe in Hsafe;
        apply Hsafe;
        lia
    end.
  }
  assert (Hlow : INT_MIN <= cur + Znth i l 0) by lia.
  assert (Hhigh : cur + Znth i l 0 <= INT_MAX) by lia.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      match goal with
      | Hlen : Zlength l = n_pre |- _ => exact Hlen
      end.
    + dump_pre_spatial.
      match goal with
      | Hsafe : kadane_safe l |- _ => exact Hsafe
      end.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      exact Hlow.
    + dump_pre_spatial.
      exact Hhigh.
    + dump_pre_spatial.
      match goal with
      | Hcur : cur = max_suffix_sum (sublist 0 i l) |- _ => exact Hcur
      end.
    + dump_pre_spatial.
      match goal with
      | Hres : res = max_subarray_sum (sublist 0 i l) |- _ => exact Hres
      end.
Qed.

Lemma proof_of_max_sub_array_entail_wit_3 : max_sub_array_entail_wit_3.
Proof.
  pre_process.
  assert (Hprefix_nonempty : sublist 0 i l <> nil).
  {
    intro Hnil.
    assert (Hlen : Zlength (sublist 0 i l) = i)
      by (rewrite Zlength_sublist0; lia).
    rewrite Hnil in Hlen.
    rewrite Zlength_nil in Hlen.
    lia.
  }
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      match goal with
      | Hlen : Zlength l = n_pre |- _ => exact Hlen
      end.
    + dump_pre_spatial.
      match goal with
      | Hsafe : kadane_safe l |- _ => exact Hsafe
      end.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      subst retval cur.
      pose proof Zlength_correct l as Hzlen.
      assert (Hlo : 0 <= 0 <= i) by lia.
      assert (Hhi : i <= i + 1 <= Z.of_nat (length l))
        by (rewrite <- Hzlen; lia).
      pose proof (sublist_split 0 (i + 1) i l) as Hsplit.
      specialize (Hsplit Hlo Hhi).
      rewrite Hsplit.
      assert (Hsingle_cond : 0 <= i < Z.of_nat (length l))
        by (rewrite <- Hzlen; lia).
      pose proof (sublist_single i l 0) as Hsingle.
      specialize (Hsingle Hsingle_cond).
      rewrite Hsingle.
      rewrite max_suffix_sum_snoc by exact Hprefix_nonempty.
      reflexivity.
    + dump_pre_spatial.
      match goal with
      | Hres : res = max_subarray_sum (sublist 0 i l) |- _ => exact Hres
      end.
Qed.

Lemma proof_of_max_sub_array_entail_wit_4 : max_sub_array_entail_wit_4.
Proof.
  pre_process.
  assert (Hprefix_nonempty : sublist 0 i l <> nil).
  {
    intro Hnil.
    assert (Hlen : Zlength (sublist 0 i l) = i)
      by (rewrite Zlength_sublist0; lia).
    rewrite Hnil in Hlen.
    rewrite Zlength_nil in Hlen.
    lia.
  }
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      match goal with
      | Hlen : Zlength l = n_pre |- _ => exact Hlen
      end.
    + dump_pre_spatial.
      match goal with
      | Hsafe : kadane_safe l |- _ => exact Hsafe
      end.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      match goal with
      | Hcur : cur = max_suffix_sum (sublist 0 (i + 1) l) |- _ => exact Hcur
      end.
    + dump_pre_spatial.
      subst retval cur res.
      pose proof Zlength_correct l as Hzlen.
      assert (Hlo : 0 <= 0 <= i) by lia.
      assert (Hhi : i <= i + 1 <= Z.of_nat (length l))
        by (rewrite <- Hzlen; lia).
      pose proof (sublist_split 0 (i + 1) i l) as Hsplit.
      specialize (Hsplit Hlo Hhi).
      rewrite Hsplit.
      assert (Hsingle_cond : 0 <= i < Z.of_nat (length l))
        by (rewrite <- Hzlen; lia).
      pose proof (sublist_single i l 0) as Hsingle.
      specialize (Hsingle Hsingle_cond).
      rewrite Hsingle.
      rewrite max_subarray_sum_snoc by exact Hprefix_nonempty.
      reflexivity.
Qed.

Lemma proof_of_max_sub_array_entail_wit_6 : max_sub_array_entail_wit_6.
Proof.
  pre_process.
  replace i with (Zlength l) in * by lia.
  rewrite sublist_self in * by reflexivity.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      match goal with
      | Hlen : Zlength l = n_pre |- _ => exact Hlen
      end.
    + dump_pre_spatial.
      match goal with
      | Hsafe : kadane_safe l |- _ => exact Hsafe
      end.
    + dump_pre_spatial.
      match goal with
      | Hcur : cur = max_suffix_sum l |- _ => exact Hcur
      end.
    + dump_pre_spatial.
      match goal with
      | Hres : res = max_subarray_sum l |- _ => exact Hres
      end.
Qed.

Lemma proof_of_max_sub_array_return_wit_2 : max_sub_array_return_wit_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      subst res.
      apply max_subarray_sum_intuitive.
      intro Hnil.
      rewrite Hnil in H0.
      rewrite Zlength_nil in H0.
      lia.
Qed.
