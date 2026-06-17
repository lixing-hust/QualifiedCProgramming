Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma ptr_array2_strategy1_correctness : ptr_array2_strategy1.
Proof.
  pre_process_default.
  prop_apply (CharPtrArray2.full_Zlength p n rows).
  Intros.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i p i n rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
     change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows
__default_app1_Z)) (Znth i rows __default_app1_Z)) with (CharArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)).
    entailer!.
    Intros_r v.
    apply_sepcon_adjoint.
    Intros.
    subst v.
    cancel.
Qed.

Lemma ptr_array2_strategy4_correctness : ptr_array2_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst rows2.
  cancel.
Qed.

Lemma ptr_array2_strategy5_correctness : ptr_array2_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma ptr_array2_strategy2_correctness : ptr_array2_strategy2.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
        p i n row_ptr rows (Znth i rows __default_app1_Z)).
  unfold StorePtrAsElement.storeA in H1.
  rewrite sizeof_ptr.
  change (CharPtrArray2.ElemArray.full row_ptr
(Zlength (Znth i rows __default_app1_Z))
(Znth i rows __default_app1_Z)) with (CharArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)) in H1.
  sep_apply H1 ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma ptr_array2_strategy11_correctness : ptr_array2_strategy11.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PtrArray.seg_split_to_missing_i p x i y l 0).
  - dump_pre_spatial.
    lia.
  - cancel (PtrArray.missing_i p i x y l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    cancel.
Qed.

Lemma ptr_array2_strategy12_correctness : ptr_array2_strategy12.
Proof.
  pre_process_default.
  unfold StorePtrAsElement.storeA.
  rewrite sizeof_ptr.
  sep_apply_l_atomic (PtrArray.missing_i_merge_to_seg p x i y v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma ptr_array2_strategy13_correctness : ptr_array2_strategy13.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PtrArray.seg_split_to_seg p x y z l3).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma ptr_array2_strategy14_correctness : ptr_array2_strategy14.
Proof.
  pre_process_default.
  rewrite PtrArray.seg_empty.
  entailer!.
Qed.

Lemma ptr_array2_strategy15_correctness : ptr_array2_strategy15.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PtrArray.undef_seg_split_to_undef_seg p x y z).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma ptr_array2_strategy16_correctness : ptr_array2_strategy16.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PtrArray.seg_merge_to_seg p x y z l1 l2).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.
