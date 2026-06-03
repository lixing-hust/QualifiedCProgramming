Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_79_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_79.
Local Open Scope sac.

Lemma chararray_seg_snoc_79 : forall x lo hi l v,
  Zlength l = hi - lo ->
  ((x + hi * sizeof(CHAR)) # Char |-> v) ** CharArray.seg x lo hi l |--
  CharArray.seg x lo (hi + 1) (l ++ v :: nil).
Proof.
  intros x lo hi l.
  revert lo hi.
  induction l; intros lo hi v Hlen.
  - rewrite Zlength_nil in Hlen.
    replace hi with lo by lia.
    rewrite (CharArray.seg_empty x lo lo).
    rewrite (CharArray.seg_unfold x lo (lo + 1) nil v).
    rewrite (CharArray.seg_empty x (lo + 1) (lo + 1)).
    entailer!.
  - rewrite Zlength_cons in Hlen.
    rewrite (CharArray.seg_unfold x lo hi l a).
    rewrite <- app_comm_cons.
    rewrite (CharArray.seg_unfold x lo (hi + 1) (l ++ v :: nil) a).
    assert (Htail: Zlength l = hi - (lo + 1)) by lia.
    sep_apply (IHl (lo + 1) hi v Htail).
    entailer!.
Qed.

Lemma chararray_seg_app_79 : forall x lo mid hi l1 l2,
  Zlength l1 = mid - lo ->
  CharArray.seg x lo mid l1 ** CharArray.seg x mid hi l2 |--
  CharArray.seg x lo hi (l1 ++ l2).
Proof.
  intros x lo mid hi l1.
  revert lo mid.
  induction l1; intros lo mid l2 Hlen.
  - rewrite Zlength_nil in Hlen.
    replace mid with lo by lia.
    rewrite (CharArray.seg_empty x lo lo).
    simpl. entailer!.
  - rewrite Zlength_cons in Hlen.
    rewrite (CharArray.seg_unfold x lo mid l1 a).
    simpl.
    rewrite (CharArray.seg_unfold x lo hi (l1 ++ l2) a).
    assert (Htail: Zlength l1 = mid - (lo + 1)) by lia.
    sep_apply (IHl1 (lo + 1) mid l2 Htail).
    entailer!.
Qed.

Lemma chararray_seg_to_full_79 : forall x n l,
  CharArray.seg x 0 n l |-- CharArray.full x n l.
Proof.
  intros.
  unfold CharArray.seg, CharArray.full.
  entailer!.
Qed.

Lemma chararray_point_seg_cons_79 : forall x lo hi v l,
  ((x + lo * sizeof(CHAR)) # Char |-> v) **
    CharArray.seg x (lo + 1) hi l |--
  CharArray.seg x lo hi (v :: l).
Proof.
  intros.
  rewrite (CharArray.seg_unfold x lo hi l v).
  entailer!.
Qed.

Lemma chararray_full_join_79 : forall out total payload,
  Zlength payload = total ->
  CharArray.full out 2 (100 :: 98 :: nil) **
  CharArray.seg out 2 (total + 2) payload **
  CharArray.seg out (total + 2) (total + 5) (100 :: 98 :: 0 :: nil)
  |-- CharArray.full out (total + 5)
        ((100 :: 98 :: nil) ++ payload ++ (100 :: 98 :: 0 :: nil)).
Proof.
  intros out total payload Hpayload.
  sep_apply (CharArray.full_to_seg out 2 (100 :: 98 :: nil)).
  assert (Hprefix: Zlength (100 :: 98 :: nil) = 2 - 0)
    by (rewrite Zlength_cons, Zlength_cons, Zlength_nil; lia).
  sep_apply (chararray_seg_app_79 out 0 2 (total + 2)
    (100 :: 98 :: nil) payload Hprefix).
  assert (Hcombined:
    Zlength ((100 :: 98 :: nil) ++ payload) = (total + 2) - 0).
  { rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_cons, Zlength_nil.
    lia. }
  eapply derivable1_trans with
    (y := CharArray.seg out 0 (total + 5)
            (((100 :: 98 :: nil) ++ payload) ++ (100 :: 98 :: 0 :: nil))).
  - apply (chararray_seg_app_79 out 0 (total + 2) (total + 5)
      ((100 :: 98 :: nil) ++ payload) (100 :: 98 :: 0 :: nil) Hcombined).
  - apply chararray_seg_to_full_79.
Qed.

Lemma proof_of_decimal_to_binary_safety_wit_24 : decimal_to_binary_safety_wit_24.
Proof.
  unfold decimal_to_binary_safety_wit_24.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  match goal with
  | Hstate: binary_count_state_z ?d 0 ?b |- _ =>
      pose proof (binary_count_state_done d b ltac:(lia) Hstate)
  end.
  pose proof (binary_digits_z_length_pos_le decimal_pre ltac:(lia)).
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_31 : decimal_to_binary_safety_wit_31.
Proof.
  unfold decimal_to_binary_safety_wit_31.
  intros.
  pre_process.
  pose proof (binary_digits_z_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits_z decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_36 : decimal_to_binary_safety_wit_36.
Proof.
  unfold decimal_to_binary_safety_wit_36.
  intros.
  pre_process.
  pose proof (binary_digits_z_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits_z decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_39 : decimal_to_binary_safety_wit_39.
Proof.
  unfold decimal_to_binary_safety_wit_39.
  intros.
  pre_process.
  pose proof (binary_digits_z_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits_z decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_42 : decimal_to_binary_safety_wit_42.
Proof.
  unfold decimal_to_binary_safety_wit_42.
  intros.
  pre_process.
  pose proof (binary_digits_z_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits_z decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_45 : decimal_to_binary_safety_wit_45.
Proof.
  unfold decimal_to_binary_safety_wit_45.
  intros.
  pre_process.
  pose proof (binary_digits_z_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits_z decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_52 : decimal_to_binary_safety_wit_52.
Proof.
  unfold decimal_to_binary_safety_wit_52.
  intros.
  pre_process.
  pose proof (Z.mod_pos_bound num 2 ltac:(lia)).
  pose proof (Z.rem_bound_pos num 2 ltac:(lia) ltac:(lia)).
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_1 : decimal_to_binary_entail_wit_1.
Proof.
  unfold decimal_to_binary_entail_wit_1.
  intros.
  pre_process.
  entailer!.
  apply binary_count_state_init; lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_2 : decimal_to_binary_entail_wit_2.
Proof.
  unfold decimal_to_binary_entail_wit_2.
  intros.
  pre_process.
  replace (x ÷ 2) with (x / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_step; [lia | assumption].
  - apply (binary_count_state_step_safe decimal_pre x bits); lia || assumption.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_3 : decimal_to_binary_entail_wit_3.
Proof.
  unfold decimal_to_binary_entail_wit_3.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  match goal with
  | Hstate: binary_count_state_z ?d 0 ?b |- _ =>
      pose proof (binary_count_state_done d b ltac:(lia) Hstate)
  end.
  rewrite (CharArray.seg_empty retval 2 2).
  unfold repeat_Z; simpl.
  rewrite (CharArray.full_unfold retval 2 (98 :: nil) 100).
  rewrite (CharArray.seg_unfold retval 1 2 nil 98).
  rewrite (CharArray.seg_empty retval 2 2).
  change (retval + 0) with (retval + 0 * sizeof(CHAR)).
  change (retval + match sizeof(CHAR) with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'
                   | Z.neg y' => Z.neg y'
                   end) with (retval + 1 * sizeof(CHAR)).
  entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_4 : decimal_to_binary_entail_wit_4.
Proof.
  unfold decimal_to_binary_entail_wit_4.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  replace (i + 1 + 2) with ((i + 2) + 1) by lia.
  assert (Hlen: Zlength (repeat_Z 0 i) = (i + 2) - 2).
  { rewrite Zlength_repeat_Z by lia. lia. }
  sep_apply (chararray_seg_snoc_79 out 2 (i + 2) (repeat_Z 0 i) 0 Hlen).
  entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_5 : decimal_to_binary_entail_wit_5.
Proof.
  unfold decimal_to_binary_entail_wit_5.
  intros.
  pre_process.
  assert (i = total) by lia; subst i.
  entailer!.
  unfold CharArray.undef_seg, store_undef_array.
  replace (Z.to_nat (total + 5 - (total + 2))) with 3%nat by lia.
  replace (Z.to_nat (total + 4 - (total + 2))) with 2%nat by lia.
  replace (Z.to_nat (total + 5 - (total + 4))) with 1%nat by lia.
  simpl.
  replace (total + 2 + 1 + 1) with (total + 4) by lia.
  entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_6 : decimal_to_binary_entail_wit_6.
Proof.
  unfold decimal_to_binary_entail_wit_6.
  intros.
  pre_process.
  entailer!.
  unfold CharArray.undef_seg, CharArray.seg, store_undef_array, store_array.
  replace (Z.to_nat (total + 4 - (total + 2))) with 2%nat by lia.
  replace (Z.to_nat (total + 3 - (total + 2))) with 1%nat by lia.
  replace (Z.to_nat (total + 4 - (total + 3))) with 1%nat by lia.
  replace (Z.to_nat (total + 5 - (total + 4))) with 1%nat by lia.
  replace (Z.to_nat (total + 5 - (total + 4 + 1))) with 0%nat by lia.
  simpl.
  replace (total + 4 + 1) with (total + 5) by lia.
  replace (total + 2 + 1) with (total + 3) by lia.
  entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_7 : decimal_to_binary_entail_wit_7.
Proof.
  unfold decimal_to_binary_entail_wit_7.
  intros.
  pre_process.
  rewrite (CharArray.seg_unfold out (total + 3) (total + 5) (0 :: nil) 98).
  replace (total + 3 + 1) with (total + 4) by lia.
  rewrite (CharArray.undef_seg_empty out (total + 4)).
  entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_8 : decimal_to_binary_entail_wit_8.
Proof.
  unfold decimal_to_binary_entail_wit_8.
  intros.
  pre_process.
  Exists (List.app (100 :: 98 :: nil)
          (List.app (repeat_Z 0 total) (100 :: 98 :: nil))).
  replace (total + 2 + 1) with (total + 3) by lia.
  rewrite (CharArray.undef_seg_empty out (total + 3)).
  entailer!.
  - replace (total + 3) with (total + 2 + 1) by lia.
    sep_apply (chararray_point_seg_cons_79 out (total + 2) (total + 5)
      100 (98 :: 0 :: nil)).
    assert (Hpayload: Zlength (repeat_Z 0 total) = total).
    { rewrite Zlength_repeat_Z by
        (pose proof (Zlength_nonneg (binary_digits_z decimal_pre)); lia).
      reflexivity. }
    sep_apply (chararray_full_join_79 out total (repeat_Z 0 total) Hpayload).
    repeat rewrite <- app_assoc.
    entailer!.
  - subst bits.
    rewrite H5.
    apply decimal_binary_full_state_init; lia.
  - rewrite Zlength_app.
    change (Zlength (100 :: 98 :: nil)) with 2.
    rewrite Zlength_app.
    rewrite Zlength_repeat_Z by
      (pose proof (Zlength_nonneg (binary_digits_z decimal_pre)); lia).
    change (Zlength (100 :: 98 :: nil)) with 2.
    lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_9 : decimal_to_binary_entail_wit_9.
Proof.
  unfold decimal_to_binary_entail_wit_9.
  intros.
  pre_process.
  subst orig num x bits.
  Exists out_l_2.
  entailer!.
  pose proof (Zlength_nonneg (binary_digits_z decimal_pre)); lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_10 : decimal_to_binary_entail_wit_10.
Proof.
  unfold decimal_to_binary_entail_wit_10.
  intros.
  pre_process.
  match goal with
  | Hstate: decimal_binary_full_state_z orig num bits out_l_2 |- _ =>
      pose proof (decimal_binary_full_state_positive_digits orig num bits out_l_2
        ltac:(lia) Hstate)
  end.
  Exists out_l_2.
  replace (bits - 1 + 1) with bits by lia.
  entailer!; lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_11 : decimal_to_binary_entail_wit_11.
Proof.
  unfold decimal_to_binary_entail_wit_11.
  intros.
  pre_process.
  replace (num ÷ 2) with (num / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem num 2) with (num mod 2)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth (bits + 2) (signed_last_nbits (48 + num mod 2) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply decimal_binary_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_decimal_to_binary_return_wit_1 : decimal_to_binary_return_wit_1.
Proof.
  unfold decimal_to_binary_return_wit_1.
  intros.
  pre_process.
  assert (num = 0) by lia; subst num.
  match goal with
  | Hstate: decimal_binary_full_state_z orig 0 bits out_l_2 |- _ =>
      let Hcopy := fresh "Hstate_copy" in
      pose proof Hstate as Hcopy;
      destruct Hcopy as [payload [Hpayload Hout]];
      unfold binary_fill_full_state_z, base_fill_full_state_z in Hpayload;
      destruct Hpayload as [suffix [[_ [_ [Hdigits _]]] _]];
      unfold base_digits_pos_z in Hdigits;
      replace (Z.leb 0 0) with true in Hdigits by
        (symmetry; apply Z.leb_le; lia);
      simpl in Hdigits;
      subst bits;
      pose proof (decimal_binary_full_state_done orig out_l_2 ltac:(lia) Hstate)
        as Hdone
  end.
  Exists out_l_2 (total + 4).
  entailer!.
  - replace (total + 4 + 1) with (total + 5) by lia.
    entailer!.
  - subst orig.
    apply problem_79_spec_z_intro; [lia | assumption].
  - subst orig.
    pose proof (binary_digits_z_length_pos_le decimal_pre ltac:(lia)).
    pose proof (Zlength_nonneg (binary_digits_z decimal_pre)).
    lia.
Qed. 

Lemma proof_of_decimal_to_binary_return_wit_2 : decimal_to_binary_return_wit_2.
Proof.
  unfold decimal_to_binary_return_wit_2.
  intros.
  pre_process.
  subst decimal_pre.
  Exists ((100 :: 98 :: 48 :: 100 :: 98 :: nil) : list Z) 5.
  rewrite (CharArray.undef_seg_empty retval 6).
  entailer!.
  - change (List.app (100 :: 98 :: 48 :: 100 :: 98 :: nil) (0 :: nil))
      with (100 :: 98 :: 48 :: 100 :: 98 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (5 + 1)
      (98 :: 48 :: 100 :: 98 :: 0 :: nil) 100).
    rewrite (CharArray.seg_unfold retval 1 (5 + 1)
      (48 :: 100 :: 98 :: 0 :: nil) 98).
    rewrite (CharArray.seg_unfold retval 2 (5 + 1)
      (100 :: 98 :: 0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 3 (5 + 1)
      (98 :: 0 :: nil) 100).
    rewrite (CharArray.seg_unfold retval 4 (5 + 1)
      (0 :: nil) 98).
    rewrite (CharArray.seg_unfold retval 5 (5 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 6 6).
    entailer!.
Qed. 
