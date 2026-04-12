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
From SimpleC.EE.Applications.minigmp Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications.minigmp Require Import GmpAux GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_gmp_abs_return_wit_2 : gmp_abs_return_wit_2.
Proof. pre_process. Qed. 

Lemma proof_of_gmp_abs_return_wit_1 : gmp_abs_return_wit_1.
Proof. pre_process. Qed.  

Lemma proof_of_gmp_max_return_wit_2 : gmp_max_return_wit_2.
Proof. pre_process. Qed. 

Lemma proof_of_gmp_max_return_wit_1 : gmp_max_return_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_gmp_cmp_return_wit_2 : gmp_cmp_return_wit_2.
Proof.
  pre_process. 
  Left. Left. entailer!.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Proof.
  pre_process.
  pose proof (Zlength_nonneg l).
  entailer!.
  rewrite UIntArray.full_empty.
  sep_apply UIntArray.undef_full_to_undef_seg.
  entailer!.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  sep_apply UIntArray.seg_single.
  sep_apply UIntArray.full_to_seg.
  sep_apply UIntArray.seg_merge_to_full ; try lia.
  replace (d_pre + 0 * sizeof ( UINT )) with (d_pre) by lia.
  replace (i + 1 - 0) with (i + 1) by lia.
  rewrite Zlength_correct in H2.
  rewrite (sublist_split 0 (i + 1) i) ; try lia.
  rewrite <- sublist_single ; try lia.
  entailer!.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1 : mpn_copyi_return_wit_1.
Proof. 
  pre_process.
  unfold mpd_store_Z , mpd_store_list. 
  Exists l l.
  assert (i = n_pre) by lia.
  subst i.
  rewrite sublist_self ; try lia.
  entailer!.
  rewrite UIntArray.undef_seg_empty.
  subst n_pre.
  entailer!.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Proof. 
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l. 
  Exists l. subst n.
  entailer!.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Proof. 
  pre_process.
  entailer!.
  replace (n_pre - 1 + 1) with (n_pre) by lia.
  rewrite sublist_nil ; try lia.
  rewrite sublist_nil ; try lia.
  auto.
Qed. 

Lemma proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  replace (n - 1 + 1) with n by lia.
  rewrite Zlength_correct in *.
  do 2 (rewrite (sublist_split n n_pre (n + 1)) ; try lia).
  rewrite H3.
  rewrite (sublist_single n l1 0) ; try lia.
  rewrite (sublist_single n l2 0) ; try lia.
  rewrite H.
  reflexivity.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Proof. 
  pre_process.
  Left. Left.
  entailer!.
  + unfold mpd_store_Z_compact.
    Exists l1 l2.
    unfold mpd_store_list.
    entailer!.
    rewrite <-H11, <-H12.
    entailer!.
  + assert (Znth n l1 0 < Znth n l2 0) by lia. 
    unfold UINT_MOD in *.
    rewrite <- H5, <- H8.
    apply (list_to_Z_cmp_same_length 4294967296 (ltac:(lia)) l1 l2 n) ; auto ; try lia.
    rewrite <- H11, <-H12.
    auto.
Qed. 

Lemma proof_of_mpn_cmp_return_wit_1 : mpn_cmp_return_wit_1.
Proof.
  pre_process.
  Right.
  entailer!.
  + unfold mpd_store_Z_compact.
    Exists l1 l2.
    unfold mpd_store_list.
    entailer!.
    rewrite <-H11, <-H12.
    entailer!.
  + pose proof (list_to_Z_cmp_same_length 4294967296 (ltac:(lia)) l2 l1 n) .
    rewrite <- H11, <- H12 in H14.
    unfold UINT_MOD in *.
    rewrite <- H5, <- H8.
    specialize (H14 (ltac:(lia)) (ltac:(lia)) (ltac:(auto)) H10 H7 (ltac:(lia))).
    lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3 : mpn_cmp_return_wit_3.
Proof. 
  pre_process.
  Left. Right.
  unfold mpd_store_Z_compact.
  Exists l1 l2.
  unfold mpd_store_list.
  rewrite <- H3, <- H6.
  rewrite <- H9, <- H10.
  entailer!.
  replace (n + 1) with 0 in * by lia.
  do 2 rewrite sublist_self in * by lia.
  subst. auto.
Qed. 

Lemma proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  entailer!.
Qed. 

Lemma proof_of_mpn_cmp4_return_wit_2 : mpn_cmp4_return_wit_2.
Proof.
  pre_process.
  Right.
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  entailer!.
  unfold UINT_MOD in *.
  pose proof list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) l2 l1 (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia)).
  lia. 
Qed. 

Lemma proof_of_mpn_cmp4_return_wit_1 : mpn_cmp4_return_wit_1.
Proof.
  pre_process.
  Left. Left.
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  entailer!.
  unfold UINT_MOD in *.
  pose proof list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) l1 l2 (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_5 : mpn_cmp4_return_wit_5.
Proof.
  pre_process.
  Right. subst.
  entailer!.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_4 : mpn_cmp4_return_wit_4.
Proof.
  pre_process.
  Left. Right. subst.
  entailer!.
Qed. 

Lemma proof_of_mpn_cmp4_return_wit_3 : mpn_cmp4_return_wit_3.
Proof.
  pre_process.
  Left. Left. subst.
  entailer!.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Proof.
  pre_process.
  rewrite sublist_self ; try lia.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3 : mpn_normalized_size_entail_wit_3.
Proof.
  pre_process.
  rewrite Zlength_correct in H7.
  rewrite Znth_sublist in H ; try lia.
  replace (n - 1 + 0) with (n - 1) in * by lia.
  rewrite (sublist_split 0 n (n-1)) in *  ; try lia.
  set (m := n - 1) in *.
  replace n with (m + 1) in * by lia.
  rewrite (sublist_single m l 0) in * ; try lia.
  rewrite H in *.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat in H3 ; [ | lia | apply list_within_bound_sublist ; [ lia | rewrite Zlength_correct ; lia | tauto] | simpl ; lia].
  sep_apply (UIntArray.full_split_to_seg xp_pre m) ; try lia.
  sep_apply (UIntArray.seg_to_undef_seg xp_pre m ).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg ; try lia.
  sep_apply UIntArray.seg_to_full.
  replace (xp_pre + 0 * sizeof ( UINT )) with (xp_pre) by lia.
  replace (m - 0) with m by lia.
  assert (m = Zlength(sublist 0 m l)).
  {
    rewrite Zlength_sublist ; try lia.
    rewrite Zlength_correct. lia.
  }
  rewrite H11 at 2.
  rewrite sublist_app_exact1.
  simpl in H3.
  entailer!.
  rewrite Zlength_correct. lia.
Qed. 

Lemma proof_of_mpn_normalized_size_return_wit_2 : mpn_normalized_size_return_wit_2.
Proof.
  pre_process.
  unfold mpd_store_Z_compact.
  assert (n = 0) by lia.
  subst n.
  rewrite sublist_nil in * ; try lia.
  unfold mpd_store_list.
  Exists nil.
  entailer!.
Qed. 

Lemma proof_of_mpn_normalized_size_return_wit_1 : mpn_normalized_size_return_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Exists (sublist 0 n l).
  rewrite Zlength_sublist ; try lia.
  replace (n - 0) with n by lia.
  pose proof (list_within_bound_sublist UINT_MOD l 0 n (ltac:(lia)) (ltac:(lia)) (ltac:(tauto))).
  entailer!.
  rewrite list_last_to_Znth.
  + rewrite Zlength_sublist ; try lia.
    replace (n - 0 -  1) with (n - 1) by lia.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos (sublist 0 n l) (n - 1) (ltac:(lia)) (ltac:(tauto))).
    lia.
  + intro. rewrite H10 in H. 
    apply H. unfold Znth. simpl. 
    destruct (Z.to_nat (n - 1)) ; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z.
  unfold mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  entailer!.
Qed. 


Lemma proof_of_mpn_add_1_entail_wit_2_1 : mpn_add_1_entail_wit_2_1.
Proof.
  pre_process.
  replace (0 + 1) with 1 by lia.
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with (rp_pre) by lia.
  replace (0 + 1 - 0) with 1 by lia.
  Exists (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (list_to_Z UINT_MOD (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil)).
  entailer! ; unfold UINT_MOD in * ; simpl ; pose proof (unsigned_Lastnbits_range (Znth 0 l 0 + b_pre) 32) ; try lia.
  replace 1 with (0 + 1) at 1 by lia.
  rewrite Zlength_correct in H0.
  rewrite (sublist_single 0 l 0) ; try lia.
  simpl.
  unfold unsigned_last_nbits in *.
  replace (2 ^ 32) with 4294967296 in * by reflexivity.
  apply Z_mod_add_carry in H ; try lia.
  apply list_within_bound_Znth ; try lia. auto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_2_2 : mpn_add_1_entail_wit_2_2.
Proof.
  pre_process.
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with (rp_pre) by lia.
  replace (0 + 1 - 0) with 1 by lia.
  Exists (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (list_to_Z UINT_MOD (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil)).
  entailer! ; unfold UINT_MOD in * ; simpl ; pose proof (unsigned_Lastnbits_range (Znth 0 l 0 + b_pre) 32) ; try lia.
  replace 1 with (0 + 1) at 1 by lia.
  rewrite Zlength_correct in H0.
  rewrite (sublist_single 0 l 0) ; try lia.
  simpl.
  unfold unsigned_last_nbits in *.
  replace (2 ^ 32) with 4294967296 in * by reflexivity.
  apply Z_mod_add_uncarry in H ; try lia.
  apply list_within_bound_Znth ; try lia. auto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_1 : mpn_add_1_entail_wit_1_1.
Proof.
  pre_process.
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  Exists (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (list_to_Z UINT_MOD (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)).
  pose proof (unsigned_Lastnbits_range (Znth i l 0 + b) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)) by (simpl ; lia).
  entailer! ; unfold UINT_MOD in * ;  try lia.
  - apply list_within_bound_concat ; try tauto.
  - rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil.
    lia.
  - rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite H8. simpl list_to_Z.
    rewrite H6.
    rewrite Zlength_correct in H10. 
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l 0 ) ; try lia.
    rewrite <- Zlength_correct in H10 ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    + rewrite H7. simpl list_to_Z.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia.
      rewrite Z.pow_add_r ; try lia.
      rewrite Z.mul_1_l.
      rewrite <- (Z.mul_comm (4294967296 ^ 1)).
      replace (4294967296 ^ 1) with 4294967296 by reflexivity.
      replace (val2_2 + unsigned_last_nbits (Znth i l 0 + b) 32 * 4294967296 ^ i + 4294967296 * 4294967296 ^ i) with (val2_2 + (unsigned_last_nbits (Znth i l 0 + b) 32 + 4294967296) * 4294967296 ^ i) by lia.
      apply Z_mod_add_carry in H ; try lia.
      unfold unsigned_last_nbits.
      replace (2 ^ 32) with 4294967296 in * by reflexivity.
      rewrite <- H.
      lia.
      apply list_within_bound_Znth ; try lia. auto.
    + apply list_within_bound_sublist ; try lia ; try tauto.
    + simpl. split ; try tauto. apply list_within_bound_Znth ; try lia. auto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_2 : mpn_add_1_entail_wit_1_2.
Proof.
  pre_process.
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  Exists (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (list_to_Z UINT_MOD (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)).
  pose proof (unsigned_Lastnbits_range (Znth i l 0 + b) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  entailer! ; unfold UINT_MOD in * ;  try lia.
  - apply list_within_bound_concat ; try tauto.
  - rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil.
    lia.
  - rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite H8. simpl list_to_Z.
    rewrite H6.
    rewrite Zlength_correct in H10. 
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l 0 ) ; try lia.
    rewrite <- Zlength_correct in H10 ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    + rewrite H7. simpl list_to_Z.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia.
      rewrite Z.mul_0_l. rewrite Z.add_0_r.
      apply Z_mod_add_uncarry in H ; try lia.
      unfold unsigned_last_nbits.
      replace (2 ^ 32) with 4294967296 in * by reflexivity.
      rewrite <- H.
      lia.
      apply list_within_bound_Znth ; try lia. auto.
    + apply list_within_bound_sublist ; try lia ; try tauto.
    + simpl. split ; try tauto. apply list_within_bound_Znth ; try lia. auto.
Qed. 

Lemma proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  assert (i = n_pre) by lia. subst i.
  rewrite H12.
  rewrite UIntArray.undef_seg_empty.
  rewrite sublist_self in H6 ; try lia.
  assert (val = val1) by lia. subst val1.
  Exists val2.
  Exists l l'.
  rewrite H9.
  rewrite H12.
  entailer!. 
  rewrite H12 in H4. lia.
Qed.

Lemma proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Proof. 
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l1.
  Exists l1.
  rewrite <- H0.
  entailer!.
Qed. 

Lemma proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Proof. 
  pre_process.
  Exists 0 nil.
  Exists 0 0.
  entailer!.
  sep_apply UIntArray.undef_full_to_undef_seg.
  rewrite UIntArray.full_empty.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_2 : mpn_add_n_entail_wit_2_2.
Proof.
  pre_process.
  sep_apply (UIntArray.seg_single rp_pre i).
  sep_apply UIntArray.seg_to_full.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32).
  entailer! ; unfold UINT_MOD in *.
  + apply Z_mod_add_uncarry in H ; try lia.
    rewrite H10.
    rewrite Z.pow_add_r ; try lia.
    rewrite Z.mul_1_l.
    rewrite <- (Z.mul_comm (4294967296 ^ 1)).
    replace (4294967296 ^ 1) with 4294967296 by reflexivity.
    replace (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ i + 4294967296 * 4294967296 ^ i) with (val_r_2 + (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 + 4294967296) * 4294967296 ^ i) by lia.
    unfold unsigned_last_nbits in *.
    rewrite <- H.
    apply Z_mod_add_carry in H0 ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    simpl list_to_Z. lia.
  + rewrite Zlength_correct in H13.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_b 0) ; try lia.
    rewrite <- Zlength_correct in H13.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite Zlength_correct in H12.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_a 0) ; try lia.
    rewrite <- Zlength_correct in H12.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_1 : mpn_add_n_entail_wit_2_1.
Proof. 
  pre_process.
  sep_apply (UIntArray.seg_single rp_pre i).
  sep_apply UIntArray.seg_to_full.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32).
  entailer! ; unfold UINT_MOD in *.
  + apply Z_mod_add_carry in H ; try lia.
    rewrite H10.
    replace ((1 + 1) * 4294967296 ^ (i + 1)) with (4294967296 ^ (i + 1) + 4294967296 ^ (i + 1)) by lia.
    rewrite Z.pow_add_r ; try lia.
    rewrite <- (Z.mul_comm (4294967296 ^ 1)).
    replace (4294967296 ^ 1) with 4294967296 by reflexivity.
    replace (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ i + (4294967296 * 4294967296 ^ i + 4294967296 * 4294967296 ^ i) ) with (val_r_2 + (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 + 4294967296 + 4294967296) * 4294967296 ^ i) by lia.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    rewrite <- H.
    apply Z_mod_add_carry in H0 ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    simpl list_to_Z. lia.
  + rewrite Zlength_correct in H13.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_b 0) ; try lia.
    rewrite <- Zlength_correct in H13.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite Zlength_correct in H12.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_a 0) ; try lia.
    rewrite <- Zlength_correct in H12.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed. 

Lemma proof_of_mpn_add_n_entail_wit_2_4 : mpn_add_n_entail_wit_2_4.
Proof.
  pre_process.
  sep_apply (UIntArray.seg_single rp_pre i).
  sep_apply UIntArray.seg_to_full.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32).
  entailer! ; unfold UINT_MOD in *.
  + apply Z_mod_add_uncarry in H ; try lia.
    rewrite H10.
    rewrite Z.pow_add_r ; try lia.
    rewrite Z.mul_0_l. rewrite Z.add_0_r.
    unfold unsigned_last_nbits in *.
    rewrite <- H.
    apply Z_mod_add_uncarry in H0 ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    simpl list_to_Z. lia.
  + rewrite Zlength_correct in H13.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_b 0) ; try lia.
    rewrite <- Zlength_correct in H13.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite Zlength_correct in H12.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_a 0) ; try lia.
    rewrite <- Zlength_correct in H12.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed. 

Lemma proof_of_mpn_add_n_entail_wit_2_3 : mpn_add_n_entail_wit_2_3.
Proof. 
  pre_process.
  sep_apply (UIntArray.seg_single rp_pre i).
  sep_apply UIntArray.seg_to_full.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32).
  entailer! ; unfold UINT_MOD in *.
  + apply Z_mod_add_carry in H ; try lia.
    rewrite H10.
    rewrite Z.pow_add_r ; try lia.
    rewrite Z.mul_1_l.
    rewrite <- (Z.mul_comm (4294967296 ^ 1)).
    replace (4294967296 ^ 1) with 4294967296 by reflexivity.
    replace (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ i + 4294967296 * 4294967296 ^ i) with (val_r_2 + (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 + 4294967296) * 4294967296 ^ i) by lia.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    rewrite <- H.
    apply Z_mod_add_uncarry in H0 ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    simpl list_to_Z. lia.
  + rewrite Zlength_correct in H13.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_b 0) ; try lia.
    rewrite <- Zlength_correct in H13.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite Zlength_correct in H12.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single i l_a 0) ; try lia.
    rewrite <- Zlength_correct in H12.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - simpl list_to_Z. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed. 

Lemma proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre) by lia. subst i.
  rewrite H17 in *.
  unfold mpd_store_Z , mpd_store_list.
  rewrite UIntArray.undef_seg_empty.
  rewrite sublist_self in H5 ; try lia.
  rewrite sublist_self in H4 ; try lia.
  Exists val_r.
  Exists l_a l_b l_r.
  rewrite H10 , H11, H17.
  entailer!. 
Qed. 

Lemma proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0 , <- H2.
  entailer!.
Qed. 


Lemma proof_of_mpn_add_return_wit_1 : mpn_add_return_wit_1.
Proof.
  pre_process.
  assert (an_pre = bn_pre) by lia. subst an_pre.
  Exists val_r_out_2.
  unfold mpd_store_Z , mpd_store_list.
  Intros la lb lr.
  Exists la lb l_r.
  replace (bn_pre - bn_pre) with 0 in * by lia.
  symmetry in H19.
  apply Zlength_nil_inv in H19.
  subst lr. simpl in *.
  destruct H18.
  subst val_a_high.
  rewrite UIntArray.full_empty.
  rewrite Zlength_nil.
  rewrite UIntArray.undef_full_empty.
  rewrite H6.
  entailer!.
Qed. 

Lemma proof_of_mpn_add_return_wit_2 : mpn_add_return_wit_2.
Proof. 
  pre_process.
  Exists (val_r_out_2 + val' * UINT_MOD ^ bn_pre).
  unfold mpd_store_Z , mpd_store_list.
  Intros la' lr' la lb.
  Exists (la ++ la') lb (l_r ++ lr').
  rewrite <- H16 , <- H18, <- H20, <- H22.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  sep_apply (UIntArray.full_merge_to_full ap_pre) ; try lia.
  repeat rewrite Zlength_app.
  rewrite H7. rewrite <- H16 , <- H18, <- H20.
  replace (bn_pre + (an_pre - bn_pre)) with an_pre by lia.
  entailer!.
  all : try apply list_within_bound_concat ; try tauto.
  all : unfold UINT_MOD in *.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite H7. lia.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite <- H20. lia.
  + replace (an_pre) with (bn_pre + (an_pre - bn_pre)) by lia.
    rewrite Z.pow_add_r ; try lia.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l.
  Exists (list_to_Z UINT_MOD (sublist bn an l)) (list_to_Z UINT_MOD (sublist 0 bn l)) .
  Exists (sublist 0 bn l) (sublist bn an l).
  rewrite Zlength_sublist ; try lia.
  sep_apply (UIntArray.full_split_to_full ap bn) ; try lia.
  rewrite <- H2.
  rewrite Zlength_sublist ; try lia.
  replace (bn - 0) with bn by lia.
  entailer!.
  all : try apply list_within_bound_sublist ; try lia ; try tauto.
  destruct H1.
  rewrite <- H1.
  rewrite <- (sublist_self l an) at 1; try lia.
  rewrite Zlength_correct in H2.
  rewrite (sublist_split 0 an bn) ; try lia.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat ; try lia.
  rewrite Zlength_sublist ; try lia.
  replace (bn - 0) with bn by lia.
  lia.
  all : 
  rewrite <- Zlength_correct in H2 ; apply list_within_bound_sublist ; try lia ; try tauto.
Qed. 

Lemma proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.
Proof.
  pre_process.
  apply UIntArray.undef_full_split_to_undef_full ; try lia.
Qed. 

Lemma proof_of_mpn_add_which_implies_wit_3 : mpn_add_which_implies_wit_3.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  entailer!.
Qed. 

Lemma proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Proof.
  pre_process.
  subst cap_2.
  assert (size_2 = 0) by lia.
  subst size_2.
  Exists ptr_2 0 0.
  entailer!.
  unfold mpd_store_Z_compact , mpd_store_list.
  Intros l.
  symmetry in H3.
  apply Zlength_nil_inv in H3.
  subst l.
  rewrite UIntArray.full_empty.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
Qed.

Lemma proof_of_mpz_clear_return_wit_1 : mpz_clear_return_wit_1.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_clear_which_implies_wit_1 : mpz_clear_which_implies_wit_1.
Proof. 
  pre_process.
  unfold store_Z.
  Intros ptr size cap.
  Split ; Intros ; [Left | Right ] ; Exists ptr cap size ;  entailer!.
Qed. 

Lemma proof_of_mpz_realloc_return_wit_8_pos : mpz_realloc_return_wit_8_pos.
Proof. 
  pre_process.
  sep_apply (UIntArray.undef_full_to_undef_seg retval) ; try lia.
  assert (old_pos = 0) by lia.
  subst old_pos cap_pos.
  unfold mpd_store_Z_compact , mpd_store_list.
  Intros l.
  symmetry in H10.
  apply Zlength_nil_inv in H10.
  subst l.
  Exists retval_2 nil.
  subst retval_2.
  do 2 rewrite UIntArray.full_empty.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_7_neg : mpz_realloc_return_wit_7_neg.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_realloc_return_wit_4_neg : mpz_realloc_return_wit_4_neg.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_realloc_return_wit_3_pos : mpz_realloc_return_wit_3_pos.
Proof. pre_process. Qed.

Lemma proof_of_mpz_realloc_return_wit_2_neg : mpz_realloc_return_wit_2_neg.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_realloc_return_wit_1_pos : mpz_realloc_return_wit_1_pos.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_realloc_partial_solve_wit_3_neg_pure : mpz_realloc_partial_solve_wit_3_neg_pure.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_realloc_partial_solve_wit_4_pos_pure : mpz_realloc_partial_solve_wit_4_pos_pure.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_realloc_partial_solve_wit_5_neg_pure : mpz_realloc_partial_solve_wit_5_neg_pure.
Proof. pre_process. Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_6_pos_pure : mpz_realloc_partial_solve_wit_6_pos_pure.
Proof. pre_process. Qed. 

Lemma proof_of_mpz_realloc_partial_solve_wit_7_neg_pure : mpz_realloc_partial_solve_wit_7_neg_pure.
Proof. pre_process. Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_9_neg_pure : mpz_realloc_partial_solve_wit_9_neg_pure.
Proof. pre_process. Qed. 


Lemma proof_of_mrz_realloc_if_return_wit_1_pos : mrz_realloc_if_return_wit_1_pos.
Proof.
  pre_process.
  Exists r_callee__mp_alloc.
  assert (Z.max (Z.max n_pre 1) cap_pos = Z.max n_pre 1).
  {
    apply Zmax_left.
    lia.
  }
  rewrite H8.
  entailer!.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_neg : mrz_realloc_if_return_wit_2_neg.
Proof.
  pre_process.
  Exists r_callee__mp_alloc.
  assert (Z.max (Z.max n_pre 1) cap_neg = Z.max n_pre 1).
  {
    apply Zmax_left.
    lia.
  }
  rewrite H8.
  entailer!.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_4_pos : mrz_realloc_if_return_wit_4_pos.
Proof.
  pre_process.
  Exists cap_pos.
  assert (Z.max (Z.max n_pre 1) cap_pos = cap_pos).
  {
    apply Zmax_right.
    apply Z.max_lub ; try lia.
  }
  rewrite H6.
  entailer!.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_3_neg : mrz_realloc_if_return_wit_3_neg.
Proof.
  pre_process.
  Exists cap_neg.
  assert (Z.max (Z.max n_pre 1) cap_neg = cap_neg).
  {
    apply Zmax_right.
    apply Z.max_lub ; try lia.
  }
  rewrite H6.
  entailer!.
Qed.

Lemma proof_of_mpz_sgn_return_wit_3 : mpz_sgn_return_wit_3.
Proof. 
  pre_process. 
  Right. unfold store_Z.
  Exists ptr size cap.
  Right.
  prop_apply (mpd_store_Z_compact_pos) ; try lia.
  Intros. entailer!.
  unfold UINT_MOD. lia.
Qed. 

Lemma proof_of_mpz_sgn_return_wit_2 : mpz_sgn_return_wit_2.
Proof.
  pre_process. 
  Left. Right. unfold store_Z.
  Exists ptr size cap.
  Right. subst size.
  prop_apply (mpd_store_Z_compact_zero) ; try lia.
  Intros. entailer!.
Qed. 

Lemma proof_of_mpz_sgn_return_wit_1 : mpz_sgn_return_wit_1.
Proof. 
  pre_process. 
  Left. Left. unfold store_Z.
  Exists ptr size cap.
  Left. entailer!.
Qed. 

Lemma proof_of_mpz_sgn_which_implies_wit_1 : mpz_sgn_which_implies_wit_1.
Proof. 
  pre_process.
  unfold store_Z.
  Intros ptr size cap.
  Split ; Intros ; [Left | Right ] ; Exists ptr cap size ;  entailer!.
Qed. 

Lemma proof_of_mpz_swap_return_wit_4 : mpz_swap_return_wit_4.
Proof. 
  pre_process.
  unfold store_Z.
  Exists ptr2 size2 cap2.
  Exists ptr1 size1 cap1.
  Left. Left. entailer!.
Qed. 

Lemma proof_of_mpz_swap_return_wit_3 : mpz_swap_return_wit_3.
Proof. 
  pre_process.
  unfold store_Z.
  Exists ptr2 size2 cap2.
  Exists ptr1 size1 cap1.
  Left. Right. entailer!.
Qed. 

Lemma proof_of_mpz_swap_return_wit_2 : mpz_swap_return_wit_2.
Proof. 
  pre_process.
  unfold store_Z.
  Exists ptr2 size2 cap2.
  Exists ptr1 size1 cap1.
  Right. Left. entailer!.
Qed.

Lemma proof_of_mpz_swap_return_wit_1 : mpz_swap_return_wit_1.
Proof. 
  pre_process.
  unfold store_Z.
  Exists ptr2 size2 cap2.
  Exists ptr1 size1 cap1.
  Right. Right. entailer!.
Qed. 

Lemma proof_of_mpz_swap_which_implies_wit_1 : mpz_swap_which_implies_wit_1.
Proof. 
  pre_process.
  pre_process.
  unfold store_Z.
  Intros ptr size cap.
  Split ; Intros ; [Left | Right ] ; Exists ptr cap size ;  entailer!.
Qed. 

Lemma proof_of_mpz_swap_which_implies_wit_2 : mpz_swap_which_implies_wit_2.
Proof. 
  pre_process.
  unfold store_Z.
  Intros ptr size cap.
  Split ; Intros ; [Left | Right ] ; Exists ptr cap size ;  entailer!.
Qed. 