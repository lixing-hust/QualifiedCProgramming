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
From SimpleC.EE Require Import C_12_goal.
From SimpleC.EE Require Import C_12_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_12.
Local Open Scope sac.

Lemma proof_of_longest_entail_wit_1_split_goal_1 : longest_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_longest_entail_wit_1 : longest_entail_wit_1.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  apply longest_prefix_z_12_initial.
Qed. 

Lemma proof_of_longest_entail_wit_2_split_goal_spatial : longest_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_longest_entail_wit_2 : longest_entail_wit_2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i strings_pre i strings_size_pre rows).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
    entailer!.
Qed. 

Lemma proof_of_longest_entail_wit_3_split_goal_1 : longest_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_longest_entail_wit_3_split_goal_2 : longest_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_longest_entail_wit_3_split_goal_3 : longest_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_longest_entail_wit_3_split_goal_spatial : longest_entail_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_longest_entail_wit_3 : longest_entail_wit_3.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  all: match goal with
  | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
      pose proof (rows_well_formed_12_row rs n i Hwf ltac:(lia))
        as [Hrow [Hvalid [Hlt Hlen]]]
  end.
  all: try solve [
    unfold store_string;
    rewrite <- Hlen;
    rewrite <- Hrow;
    entailer!
  ].
  all: try solve [exact Hlen | exact Hlt | exact Hvalid].
Qed. 

Lemma proof_of_longest_entail_wit_4_split_goal_1 : longest_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_longest_entail_wit_4_split_goal_2 : longest_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_longest_entail_wit_4_split_goal_spatial : longest_entail_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_longest_entail_wit_4 : longest_entail_wit_4.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  all: match goal with
  | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
      pose proof (rows_well_formed_12_row rs n i Hwf ltac:(lia))
        as [Hrow [Hvalid [Hlt Hlen]]]
  end.
  all: try solve [
    unfold row_len_z_12;
    pose proof (string_length_nonneg (row_payload_z_12 (Znth i rows nil)));
    lia
  ].
  all: try solve [
    unfold store_string;
    rewrite <- Hlen;
    rewrite <- Hrow;
    entailer!
  ].
Qed. 

Lemma proof_of_longest_entail_wit_5_1_split_goal_1 : longest_entail_wit_5_1_split_goal_1.
Proof. Abort.

Lemma proof_of_longest_entail_wit_5_1_split_goal_spatial : longest_entail_wit_5_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_longest_entail_wit_5_1 : longest_entail_wit_5_1.
Proof.
  pre_process_default; try entailer!; try lia.
  all: try solve [
    match goal with
    | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
        destruct Hwf as [Hrows_len Hrows_wf];
        eapply longest_prefix_z_12_step_keep; eauto; try (rewrite Hrows_len; lia); lia
    end
  ].
  all: try solve [
    pose proof (CharPtrArray2.missing_i_merge_to_full
        strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge;
    unfold StorePtrAsElement.storeA in Hmerge;
    try rewrite sizeof_ptr in Hmerge;
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge;
    try rewrite sizeof_ptr;
    sep_apply Hmerge; try lia;
    rewrite replace_Znth_Znth by lia;
    entailer!
  ].
Qed. 

Lemma proof_of_longest_entail_wit_5_2_split_goal_1 : longest_entail_wit_5_2_split_goal_1.
Proof. Abort.

Lemma proof_of_longest_entail_wit_5_2_split_goal_spatial : longest_entail_wit_5_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_longest_entail_wit_5_2 : longest_entail_wit_5_2.
Proof.
  pre_process_default; try entailer!; try lia.
  all: try solve [
    match goal with
    | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
        destruct Hwf as [Hrows_len Hrows_wf];
        eapply longest_prefix_z_12_step_update; eauto; try (rewrite Hrows_len; lia); lia
    end
  ].
  all: try solve [
    pose proof (CharPtrArray2.missing_i_merge_to_full
        strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge;
    unfold StorePtrAsElement.storeA in Hmerge;
    try rewrite sizeof_ptr in Hmerge;
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge;
    try rewrite sizeof_ptr;
    sep_apply Hmerge; try lia;
    rewrite replace_Znth_Znth by lia;
    entailer!
  ].
Qed. 

Lemma proof_of_longest_entail_wit_7 : longest_entail_wit_7.
Proof.
  pre_process_default.
  assert (Hi_eq : i = strings_size_pre) by lia.
  subst i.
  pose proof PreH8 as Hwf_all.
  destruct PreH8 as [Hrows_len Hrows_wf].
  pose proof (longest_prefix_z_12_nonempty_bounds rows strings_size_pre best_idx best PreH10 ltac:(lia)) as Hbest_bounds.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i strings_pre best_idx strings_size_pre rows).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil))
      with (CharArray.full row_ptr (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil)).
    entailer!.
    eapply longest_prefix_z_12_final_spec with (best_len := best); eauto; try lia;
      try (rewrite Hrows_len; exact Hwf_all);
      try (rewrite Hrows_len; exact PreH10).
Qed. 

Lemma proof_of_longest_return_wit_2 : longest_return_wit_2.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := “ strings_size_pre = 0 ” &&
          (“ 0 = 0 ” &&
           (“ problem_12_spec_none_z rows ” &&
            CharPtrArray2.full strings_pre strings_size_pre rows))).
  - entailer!.
    eapply problem_12_spec_none_z_intro.
    destruct PreH4 as [Hlen _].
    lia.
  - apply derivable1_orp_intros1.
Qed. 
