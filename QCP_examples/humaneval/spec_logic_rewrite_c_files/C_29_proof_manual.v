Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_29_goal.
From SimpleC.EE Require Import C_29_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.coins_29.
Local Open Scope sac.

Lemma proof_of_filter_by_prefix_entail_wit_1 : filter_by_prefix_entail_wit_1.
Proof.
  unfold filter_by_prefix_entail_wit_1.
  left. intros.
  subst strings_addr. subst prefix_addr.
  Exists (@nil Z) (@nil (list Z)).
  unfold store_string.
  entailer!.
  rewrite PtrArray.seg_empty. entailer!.
  apply filter_prefix_state_nil_29.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_2 : filter_by_prefix_entail_wit_2.
Proof.
  unfold filter_by_prefix_entail_wit_2.
  left. intros.
  pose proof (rows_well_formed_nth_29 rows strings_size_pre i PreH11 ltac:(lia))
    as Hrow.
  destruct Hrow as [Hrow_eq [Hvalid Hlen]].
  sep_apply_l_atomic
    (CharPtrArray2.full_split_to_missing_i strings_addr i strings_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr output_ptrs_2 output_rows_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr
        (Zlength (Znth i rows nil)) (Znth i rows nil)).
    unfold store_string.
    rewrite Hrow_eq, row_payload_c_string_29, c_string_Zlength_29.
    entailer!.
    unfold row_well_formed_29.
    rewrite row_payload_c_string_29. auto.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_3 : filter_by_prefix_entail_wit_3.
Proof.
  unfold filter_by_prefix_entail_wit_3.
  left. intros.
  subst retval.
  Exists output_ptrs_2 output_rows_2.
  assert (Hrow_valid : valid_string (row_payload_z_29 (Znth i rows nil))).
  { destruct PreH15 as [_ [Hvalid _]]. exact Hvalid. }
  assert (Hhit : prefix_hit_z_29
    (row_payload_z_29 (Znth i rows nil)) prefix_l).
  { eapply strncmp_zero_prefix_hit_29; eauto. }
  entailer!.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_4 : filter_by_prefix_entail_wit_4.
Proof.
  unfold filter_by_prefix_entail_wit_4.
  left. intros.
  Exists output_ptrs_2 output_rows_2.
  assert (Hmiss : prefix_miss_z_29
    (row_payload_z_29 (Znth i rows nil)) prefix_l).
  { eapply strncmp_nonzero_prefix_miss_29; eauto. }
  entailer!.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_5_1 : filter_by_prefix_entail_wit_5_1.
Proof.
  unfold filter_by_prefix_entail_wit_5_1.
  left. intros.
  pose proof (rows_well_formed_nth_29 rows strings_size_pre i PreH13 ltac:(lia))
    as Hrow.
  destruct Hrow as [Hrow_eq [Hvalid Hlen]].
  Exists (app output_ptrs_2 (cons row_ptr nil))
    (app output_rows_2
      (cons (row_payload_z_29 (Znth i rows nil)) nil)).
  pose proof (CharPtrArray2.missing_i_merge_to_full
    strings_addr i strings_size_pre row_ptr rows (Znth i rows nil)
    ltac:(lia)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
  rewrite <- (logic_equiv_sepcon_assoc
    (((strings_addr + i * 4)) # Ptr |-> row_ptr)
    (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
    (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows))
    in Hmerge.
  rewrite (logic_equiv_sepcon_comm
    (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
    (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows))
    in Hmerge.
  rewrite sizeof_ptr.
  assert (Hrawlen : Zlength (Znth i rows nil) =
    string_length (row_payload_z_29 (Znth i rows nil)) + 1).
  { rewrite Hrow_eq at 1. apply c_string_Zlength_29. }
  rewrite <- Hrawlen.
  rewrite <- Hrow_eq.
  rewrite replace_Znth_Znth in Hmerge by lia.
  entailer!.
  sep_apply_r_atomic Hmerge.
  entailer!.
  - eapply filter_prefix_state_keep_29; eauto.
    destruct PreH13 as [Hrows_len _]. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_5_2 : filter_by_prefix_entail_wit_5_2.
Proof.
  unfold filter_by_prefix_entail_wit_5_2.
  left. intros.
  pose proof (rows_well_formed_nth_29 rows strings_size_pre i PreH11 ltac:(lia))
    as Hrow.
  destruct Hrow as [Hrow_eq [Hvalid Hlen]].
  Exists output_ptrs_2 output_rows_2.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    strings_addr i strings_size_pre row_ptr rows (Znth i rows nil)
    ltac:(lia)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
  rewrite <- (logic_equiv_sepcon_assoc
    (((strings_addr + i * 4)) # Ptr |-> row_ptr)
    (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
    (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows))
    in Hmerge.
  rewrite (logic_equiv_sepcon_comm
    (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
    (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows))
    in Hmerge.
  unfold store_string.
  rewrite sizeof_ptr.
  assert (Hrawlen : Zlength (Znth i rows nil) =
    string_length (row_payload_z_29 (Znth i rows nil)) + 1).
  { rewrite Hrow_eq at 1. apply c_string_Zlength_29. }
  rewrite <- Hrawlen.
  rewrite <- Hrow_eq.
  rewrite replace_Znth_Znth in Hmerge by lia.
  entailer!.
  sep_apply_r_atomic Hmerge.
  entailer!.
  eapply filter_prefix_state_drop_29; eauto.
  destruct PreH11 as [Hrows_len _]. lia.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_6 : filter_by_prefix_entail_wit_6.
Proof.
  unfold filter_by_prefix_entail_wit_6.
  left. intros.
  assert (Hi : i = strings_size_pre) by lia. subst i.
  Exists output_ptrs_2 output_rows_2.
  assert (Hspec : problem_29_spec_z rows prefix_l output_rows_2).
  { eapply filter_prefix_state_final_29; eauto. }
  entailer!.
Qed.

Lemma proof_of_filter_by_prefix_return_wit_1 : filter_by_prefix_return_wit_1.
Proof.
  unfold filter_by_prefix_return_wit_1.
  left. intros.
  Exists output_ptrs_2 output_rows_2 output_size_2 data_2.
  entailer!.
Qed.

Lemma proof_of_filter_by_prefix_partial_solve_wit_4_pure : filter_by_prefix_partial_solve_wit_4_pure.
Proof.
  unfold filter_by_prefix_partial_solve_wit_4_pure.
  left. intros.
  unfold row_well_formed_29 in PreH11.
  destruct PreH11 as [_ [Hvalid Hlen]].
  pose proof (string_length_nonneg prefix_l).
  entailer!.
Qed.
