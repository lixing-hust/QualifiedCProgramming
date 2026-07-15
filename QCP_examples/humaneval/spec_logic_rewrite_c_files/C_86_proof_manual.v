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
From SimpleC.EE Require Import C_86_goal.
From SimpleC.EE Require Import C_86_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_86.
Local Open Scope sac.

Lemma proof_of_anti_shuffle_entail_wit_1 : anti_shuffle_entail_wit_1.
Proof.
  pre_process.
  assert (Hret_nonneg : 0 <= retval)
    by (rewrite PreH3; unfold string_length; apply Zlength_nonneg).
  rewrite <- derivable1_orp_intros2.
  Exists nil nil.
  assert (anti_shuffle_scan_state_86 str_l 0 1 nil nil) as Hinit
    by (apply anti_shuffle_initial_86; auto).
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_2 0 (retval + 1)).
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_3 0 (retval + 1)).
  rewrite (CharArray.undef_seg_empty retval_2 0).
  rewrite (CharArray.undef_seg_empty retval_3 0).
  rewrite (CharArray.full_empty retval_2 0).
  rewrite (CharArray.full_empty retval_3 0).
  entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_2_1 : anti_shuffle_entail_wit_2_1.
Proof.
  pre_process.
  pose proof PreH24 as Hstate_old.
  destruct PreH24 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hidx : 0 <= i < Zlength str_l)
    by (unfold string_length in PreH7; lia).
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127).
  { unfold c_string.
    rewrite app_Znth1 by lia.
    apply PreH20; lia. }
  replace (signed_last_nbits (Znth i (c_string str_l) 0) 8)
    with (Znth i (c_string str_l) 0)
    by (symmetry; apply signed_last_nbits_eq; lia).
  rewrite <- derivable1_orp_intros2.
  Exists (List.app cur_l_2 (Znth i (c_string str_l) 0 :: nil)) out_l_2.
  pose proof (anti_shuffle_nonspace_intro_86 str_l i first out_l_2 cur_l_2
    (Znth i (c_string str_l) 0) PreH22 Hstate_old ltac:(lia) eq_refl PreH2)
    as [Hstep Hstate].
  entailer!.
  all: rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_2_2 : anti_shuffle_entail_wit_2_2.
Proof.
  pre_process.
  pose proof PreH24 as Hstate_old.
  destruct PreH24 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hidx : 0 <= i < Zlength str_l)
    by (unfold string_length in PreH7; lia).
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127).
  { unfold c_string.
    rewrite app_Znth1 by lia.
    apply PreH20; lia. }
  replace (signed_last_nbits (Znth i (c_string str_l) 0) 8)
    with (Znth i (c_string str_l) 0)
    by (symmetry; apply signed_last_nbits_eq; lia).
  rewrite <- derivable1_orp_intros1.
  Exists (List.app cur_l_2 (Znth i (c_string str_l) 0 :: nil)) out_l_2.
  pose proof (anti_shuffle_nonspace_intro_86 str_l i first out_l_2 cur_l_2
    (Znth i (c_string str_l) 0) PreH22 Hstate_old ltac:(lia) eq_refl PreH2)
    as [Hstep Hstate].
  entailer!.
  all: rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_3_1 : anti_shuffle_entail_wit_3_1.
Proof.
  pre_process.
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH11; lia|].
    exact (or_intror PreH6). }
  rewrite <- derivable1_orp_intros1.
  Exists sorted_l_2 cur_l_2 out_l_2.
  unfold store_string.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_3_2 : anti_shuffle_entail_wit_3_2.
Proof.
  pre_process.
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH11; lia|].
    exact (or_intror PreH6). }
  rewrite <- derivable1_orp_intros2.
  Exists sorted_l_2 cur_l_2 out_l_2.
  unfold store_string.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_3_3 : anti_shuffle_entail_wit_3_3.
Proof.
  pre_process.
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH10; lia|].
    left; lia. }
  rewrite <- derivable1_orp_intros1.
  Exists sorted_l_2 cur_l_2 out_l_2.
  unfold store_string.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_3_4 : anti_shuffle_entail_wit_3_4.
Proof.
  pre_process.
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH10; lia|].
    left; lia. }
  rewrite <- derivable1_orp_intros2.
  Exists sorted_l_2 cur_l_2 out_l_2.
  unfold store_string.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_4_1 : anti_shuffle_entail_wit_4_1.
Proof.
  pre_process.
  pose proof PreH24 as Hstate_old.
  destruct PreH24 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hsort : sort_char_array_spec_86 cur_l_2 cur_l_2).
  { destruct (Z.eq_dec cur_len 0).
    - apply sort_char_array_spec_len0_86; lia.
    - apply sort_char_array_spec_len1_86; lia. }
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH7; lia|].
    exact (or_intror PreH2). }
  rewrite <- derivable1_orp_intros1.
  Exists cur_l_2 cur_l_2 out_l_2.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_4_2 : anti_shuffle_entail_wit_4_2.
Proof.
  pre_process.
  pose proof PreH24 as Hstate_old.
  destruct PreH24 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hsort : sort_char_array_spec_86 cur_l_2 cur_l_2).
  { destruct (Z.eq_dec cur_len 0).
    - apply sort_char_array_spec_len0_86; lia.
    - apply sort_char_array_spec_len1_86; lia. }
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH7; lia|].
    exact (or_intror PreH2). }
  rewrite <- derivable1_orp_intros2.
  Exists cur_l_2 cur_l_2 out_l_2.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_4_3 : anti_shuffle_entail_wit_4_3.
Proof.
  pre_process.
  pose proof PreH23 as Hstate_old.
  destruct PreH23 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hsort : sort_char_array_spec_86 cur_l_2 cur_l_2).
  { destruct (Z.eq_dec cur_len 0).
    - apply sort_char_array_spec_len0_86; lia.
    - apply sort_char_array_spec_len1_86; lia. }
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH6; lia|].
    assert (Hiend : i = string_length str_l) by (rewrite <- PreH6; lia).
    exact (or_introl Hiend). }
  rewrite <- derivable1_orp_intros1.
  Exists cur_l_2 cur_l_2 out_l_2.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_4_4 : anti_shuffle_entail_wit_4_4.
Proof.
  pre_process.
  pose proof PreH23 as Hstate_old.
  destruct PreH23 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hsort : sort_char_array_spec_86 cur_l_2 cur_l_2).
  { destruct (Z.eq_dec cur_len 0).
    - apply sort_char_array_spec_len0_86; lia.
    - apply sort_char_array_spec_len1_86; lia. }
  assert (Hcommit_index : anti_shuffle_commit_index_86 str_l i).
  { unfold anti_shuffle_commit_index_86.
    split; [rewrite <- PreH6; lia|].
    assert (Hiend : i = string_length str_l) by (rewrite <- PreH6; lia).
    exact (or_introl Hiend). }
  rewrite <- derivable1_orp_intros2.
  Exists cur_l_2 cur_l_2 out_l_2.
  entailer!.
  all: try exact Hcommit_index.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_5_1 : anti_shuffle_entail_wit_5_1.
Proof.
  left.
  intros.
  pre_process.
  pose proof PreH27 as Hstate_old.
  destruct PreH27 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hsep_space : out_len + 1 <= n).
  { specialize (Hsep_bound PreH17 ltac:(rewrite <- PreH5; lia)).
    rewrite PreH12, PreH13, <- PreH5 in Hsep_bound.
    lia. }
  Exists sorted_l_2 cur_l_2 (List.app out_l_2 (32 :: nil)) out_l_2.
  entailer!.
  all: try exact Hstate_old; try exact PreH24; try exact PreH26;
       try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_5_2 : anti_shuffle_entail_wit_5_2.
Proof.
  left.
  intros.
  pre_process.
  pose proof PreH27 as Hstate_old.
  destruct PreH27 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  destruct Hascii as [Hout_ascii Hcur_ascii].
  assert (Hsep_space : out_len + 1 <= n).
  { specialize (Hsep_bound PreH17 ltac:(rewrite <- PreH6; lia)).
    rewrite PreH13, PreH14, <- PreH6 in Hsep_bound.
    lia. }
  Exists sorted_l_2 cur_l_2 (List.app out_l_2 (32 :: nil)) out_l_2.
  entailer!.
  all: try exact Hstate_old; try exact PreH24; try exact PreH26;
       try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_6_1 : anti_shuffle_entail_wit_6_1.
Proof.
  left.
  intros.
  pre_process.
  pose proof PreH26 as Hstate_old.
  destruct PreH26 as [Hscan_i [Hfirst [Hout_len [Hout_le_i [Hcur_len_bound Hrest]]]]].
  Exists sorted_l_2 cur_l_2 out_l_2 out_l_2.
  entailer!.
  all: try exact Hstate_old; try exact PreH23; try exact PreH25;
       try rewrite PreH12 in Hcur_len_bound; try rewrite <- PreH4 in Hcur_len_bound; lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_7_1 : anti_shuffle_entail_wit_7_1.
Proof.
  pre_process.
  pose proof PreH27 as Hstate_old.
  destruct PreH27 as [Hscan_i [Hfirst [Hout_len_bound [Hout_le_i [Hcur_len_bound [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  assert (Hout_cur : out_len + cur_len <= n).
  { specialize (Hsep_bound PreH17 ltac:(rewrite <- PreH4; lia)).
    rewrite PreH11, PreH14, <- PreH4 in Hsep_bound.
    lia. }
  rewrite <- derivable1_orp_intros1.
  Exists out_l_2 out_sep_l_2 cur_l_2 sorted_l_2 out_sep_l_2.
  assert (Hcopy0 : copy_prefix_86 out_sep_l_2 sorted_l_2 0 out_sep_l_2)
    by apply copy_prefix_zero_86.
  assert (Hrel : out_sep_relation_86 first out_l_2 out_sep_l_2).
  { unfold out_sep_relation_86. left. split; auto. }
  replace (out_len + 0) with out_len by lia.
  entailer!.
  all: try exact Hstate_old; try exact PreH24; try exact PreH26; try lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_7_2 : anti_shuffle_entail_wit_7_2.
Proof.
  pre_process.
  pose proof PreH27 as Hstate_old.
  destruct PreH27 as [Hscan_i [Hfirst [Hout_len_bound [Hout_le_i [Hcur_len_bound [Hcur_le_i [Htotal_len [Hsep_bound Hascii]]]]]]]].
  assert (Hout_cur : out_len + cur_len <= n).
  { rewrite PreH4.
    rewrite <- PreH11, <- PreH14.
    exact Htotal_len. }
  rewrite <- derivable1_orp_intros2.
  Exists out_l_2 out_sep_l_2 cur_l_2 sorted_l_2 out_sep_l_2.
  assert (Hcopy0 : copy_prefix_86 out_sep_l_2 sorted_l_2 0 out_sep_l_2)
    by apply copy_prefix_zero_86.
  assert (Hrel : out_sep_relation_86 first out_l_2 out_sep_l_2).
  { unfold out_sep_relation_86. right. split; auto. }
  replace (out_len + 0) with out_len by lia.
  entailer!.
  all: try exact Hstate_old; try exact PreH24; try exact PreH26; try lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_8_1 : anti_shuffle_entail_wit_8_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  Exists out_l_2 (List.app out_copy_l_2 (signed_last_nbits (Znth copy sorted_l 0) 8 :: nil))
    cur_l_2 sorted_l out_sep_l_2.
  assert (Hcopy_step :
    copy_prefix_86 out_sep_l_2 sorted_l (copy + 1)
      (List.app out_copy_l_2 (signed_last_nbits (Znth copy sorted_l 0) 8 :: nil))).
  { apply copy_prefix_snoc_signed_86; try exact PreH24; try exact PreH22.
    rewrite PreH19; lia. }
  assert (Hzrange : 0 <= Znth copy sorted_l 0 <= 127)
    by (apply PreH24; rewrite PreH19; lia).
  replace (out_len + (copy + 1)) with ((out_len + copy) + 1) by lia.
  entailer!.
  all: try exact PreH34; try exact PreH33; try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_8_2 : anti_shuffle_entail_wit_8_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  Exists out_l_2 (List.app out_copy_l_2 (signed_last_nbits (Znth copy sorted_l 0) 8 :: nil))
    cur_l_2 sorted_l out_sep_l_2.
  assert (Hcopy_step :
    copy_prefix_86 out_sep_l_2 sorted_l (copy + 1)
      (List.app out_copy_l_2 (signed_last_nbits (Znth copy sorted_l 0) 8 :: nil))).
  { apply copy_prefix_snoc_signed_86; try exact PreH24; try exact PreH22.
    rewrite PreH19; lia. }
  assert (Hzrange : 0 <= Znth copy sorted_l 0 <= 127)
    by (apply PreH24; rewrite PreH19; lia).
  replace (out_len + (copy + 1)) with ((out_len + copy) + 1) by lia.
  entailer!.
  all: try exact PreH34; try exact PreH33; try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_10_1 : anti_shuffle_entail_wit_10_1.
Proof.
  pre_process.
  assert (Hcopy_eq : copy = cur_len) by lia.
  assert (Hout_next : out_copy_l = List.app out_sep_l_2 sorted_l_2).
  { apply copy_prefix_full_86 with (copy := copy); auto.
    rewrite PreH16; lia. }
  assert (Hcommit : anti_shuffle_commit_step_86 str_l i first out_l_2 cur_l_2 out_copy_l).
  { unfold anti_shuffle_commit_step_86.
    destruct PreH29 as [Hcommit_bounds Hcommit_case].
    split; [exact Hcommit_bounds|].
    split.
    + exact Hcommit_case.
    + exists sorted_l_2.
      split; [exact PreH31|].
      split.
      * unfold out_sep_relation_86 in PreH20.
        destruct PreH20 as [[Hfirst Hsep] | [Hfirst Hsep]]; [lia|].
        rewrite Hout_next.
        unfold emit_field_86.
        rewrite Hfirst.
        simpl.
        rewrite Hsep.
        reflexivity.
      * split; [exact PreH21|].
        rewrite <- PreH4. rewrite PreH18. rewrite Hcopy_eq. lia. }
  assert (Hnext_state : anti_shuffle_scan_state_86 str_l (i + 1) 0 out_copy_l nil)
    by (eapply anti_shuffle_commit_intro_86; eauto).
  rewrite <- derivable1_orp_intros1.
  Exists out_l_2 cur_l_2 out_copy_l sorted_l_2 out_sep_l_2.
  replace (out_len + copy) with (out_len + cur_len) by lia.
  entailer!.
  all: try exact Hcommit; try exact Hnext_state; try rewrite Hout_next;
       try rewrite Zlength_app; try lia.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_10_2 : anti_shuffle_entail_wit_10_2.
Proof.
  pre_process.
  assert (Hcopy_eq : copy = cur_len) by lia.
  assert (Hout_next : out_copy_l = List.app out_sep_l_2 sorted_l_2).
  { apply copy_prefix_full_86 with (copy := copy); auto.
    rewrite PreH16; lia. }
  assert (Hcommit : anti_shuffle_commit_step_86 str_l i first out_l_2 cur_l_2 out_copy_l).
  { unfold anti_shuffle_commit_step_86.
    destruct PreH29 as [Hcommit_bounds Hcommit_case].
    split; [exact Hcommit_bounds|].
    split.
    + exact Hcommit_case.
    + exists sorted_l_2.
      split; [exact PreH31|].
      split.
      * unfold out_sep_relation_86 in PreH20.
        destruct PreH20 as [[Hfirst Hsep] | [Hfirst Hsep]]; [|lia].
        rewrite Hout_next.
        unfold emit_field_86.
        rewrite Hfirst.
        simpl.
        rewrite Hsep.
        rewrite <- app_assoc.
        reflexivity.
      * split; [exact PreH21|].
        rewrite <- PreH4. rewrite PreH18. rewrite Hcopy_eq. lia. }
  assert (Hnext_state : anti_shuffle_scan_state_86 str_l (i + 1) 0 out_copy_l nil)
    by (eapply anti_shuffle_commit_intro_86; eauto).
  rewrite <- derivable1_orp_intros2.
  Exists out_l_2 cur_l_2 out_copy_l sorted_l_2 out_sep_l_2.
  replace (out_len + copy) with (out_len + cur_len) by lia.
  entailer!.
  all: try exact Hcommit; try exact Hnext_state; try rewrite Hout_next;
       try rewrite Zlength_app; try lia.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_11_1 : anti_shuffle_entail_wit_11_1.
Proof.
  pre_process.
  assert (Hcur0 : cur_len = 0) by lia.
  assert (Hsorted_nil : sorted_l_2 = nil).
  { apply Zlength_nil_inv. rewrite PreH15, Hcur0. reflexivity. }
  assert (Hcommit : anti_shuffle_commit_step_86 str_l i first out_l_2 cur_l_2 out_sep_l_2).
  { unfold anti_shuffle_commit_step_86.
    destruct PreH24 as [Hcommit_bounds Hcommit_case].
    split; [exact Hcommit_bounds|].
    split; [exact Hcommit_case|].
    exists sorted_l_2.
    split; [exact PreH26|].
    split.
    - unfold emit_field_86.
      rewrite PreH17.
      simpl.
      rewrite Hsorted_nil, app_nil_r.
      exact PreH12.
    - split; [exact PreH16|].
      rewrite PreH13, <- PreH4. lia. }
  assert (Hnext_state : anti_shuffle_scan_state_86 str_l (i + 1) 0 out_sep_l_2 nil)
    by (eapply anti_shuffle_commit_intro_86; eauto).
  rewrite <- derivable1_orp_intros1.
  Exists out_l_2 cur_l_2 out_sep_l_2 sorted_l_2 out_sep_l_2.
  entailer!.
  all: try exact Hcommit; try exact Hnext_state; try lia.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_11_2 : anti_shuffle_entail_wit_11_2.
Proof.
  pre_process.
  assert (Hcur0 : cur_len = 0) by lia.
  assert (Hsorted_nil : sorted_l_2 = nil).
  { apply Zlength_nil_inv. rewrite PreH15, Hcur0. reflexivity. }
  assert (Hcommit : anti_shuffle_commit_step_86 str_l i first out_l_2 cur_l_2 out_sep_l_2).
  { unfold anti_shuffle_commit_step_86.
    destruct PreH24 as [Hcommit_bounds Hcommit_case].
    split; [exact Hcommit_bounds|].
    split; [exact Hcommit_case|].
    exists sorted_l_2.
    split; [exact PreH26|].
    split.
    - unfold emit_field_86.
      rewrite PreH17.
      simpl.
      rewrite Hsorted_nil.
      exact PreH12.
    - split; [exact PreH16|].
      rewrite PreH13, <- PreH4. lia. }
  assert (Hnext_state : anti_shuffle_scan_state_86 str_l (i + 1) 0 out_sep_l_2 nil)
    by (eapply anti_shuffle_commit_intro_86; eauto).
  rewrite <- derivable1_orp_intros2.
  Exists out_l_2 cur_l_2 out_sep_l_2 sorted_l_2 out_sep_l_2.
  entailer!.
  all: try exact Hcommit; try exact Hnext_state; try lia.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_12_1_split_goal_spatial : anti_shuffle_entail_wit_12_1_split_goal_spatial.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_12_1 : anti_shuffle_entail_wit_12_1.
Proof.
  left.
  pre_process.
  assert (Hsorted_nil : sorted_l = nil).
  { apply Zlength_nil_inv. exact PreH10. }
  Exists out_next_l_2.
  subst sorted_l.
  replace cur_len with 0 by lia.
  entailer!.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_12_2_split_goal_spatial : anti_shuffle_entail_wit_12_2_split_goal_spatial.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_12_2 : anti_shuffle_entail_wit_12_2.
Proof.
  left.
  pre_process.
  assert (Hsorted_nil : sorted_l = nil).
  { apply Zlength_nil_inv. exact PreH10. }
  Exists out_next_l_2.
  subst sorted_l.
  replace cur_len with 0 by lia.
  entailer!.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_12_3_split_goal_spatial : anti_shuffle_entail_wit_12_3_split_goal_spatial.
Proof.
  pre_process.
  sep_apply (CharArray.full_to_undef_full cur cur_len sorted_l).
  sep_apply (CharArray.undef_seg_to_undef_full cur cur_len (n + 1)).
  sep_apply (CharArray.undef_full_merge_to_undef_full cur cur_len (n + 1)).
  entailer!.
  all: lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_12_3 : anti_shuffle_entail_wit_12_3.
Proof.
  right.
  apply proof_of_anti_shuffle_entail_wit_12_3_split_goal_spatial.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_12_4_split_goal_spatial : anti_shuffle_entail_wit_12_4_split_goal_spatial.
Proof.
  pre_process.
  sep_apply (CharArray.full_to_undef_full cur cur_len sorted_l).
  sep_apply (CharArray.undef_seg_to_undef_full cur cur_len (n + 1)).
  sep_apply (CharArray.undef_full_merge_to_undef_full cur cur_len (n + 1)).
  entailer!.
  all: lia.
Qed.

Lemma proof_of_anti_shuffle_entail_wit_12_4 : anti_shuffle_entail_wit_12_4.
Proof.
  right.
  apply proof_of_anti_shuffle_entail_wit_12_4_split_goal_spatial.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_13_3 : anti_shuffle_entail_wit_13_3.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  Exists (@nil Z) out_next_l.
  replace cur_len with 0 by lia.
  entailer!.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_1 : anti_shuffle_entail_wit_14_1_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_2 : anti_shuffle_entail_wit_14_1_split_goal_2.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_3 : anti_shuffle_entail_wit_14_1_split_goal_3.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_4 : anti_shuffle_entail_wit_14_1_split_goal_4.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_5 : anti_shuffle_entail_wit_14_1_split_goal_5.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_6 : anti_shuffle_entail_wit_14_1_split_goal_6.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_7 : anti_shuffle_entail_wit_14_1_split_goal_7.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_8 : anti_shuffle_entail_wit_14_1_split_goal_8.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_9 : anti_shuffle_entail_wit_14_1_split_goal_9.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_10 : anti_shuffle_entail_wit_14_1_split_goal_10.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_11 : anti_shuffle_entail_wit_14_1_split_goal_11.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_12 : anti_shuffle_entail_wit_14_1_split_goal_12.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_13 : anti_shuffle_entail_wit_14_1_split_goal_13.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_14 : anti_shuffle_entail_wit_14_1_split_goal_14.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_15 : anti_shuffle_entail_wit_14_1_split_goal_15.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1_split_goal_16 : anti_shuffle_entail_wit_14_1_split_goal_16.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_1 : anti_shuffle_entail_wit_14_1.
Proof.
  right.
  pre_process.
  subst first.
  assert (False) as Habsurd.
  { eapply anti_shuffle_terminal_first1_absurd_86; eauto.
    rewrite <- PreH5.
    lia. }
  contradiction.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_14_2_split_goal_1 : anti_shuffle_entail_wit_14_2_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_2_split_goal_2 : anti_shuffle_entail_wit_14_2_split_goal_2.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_2_split_goal_3 : anti_shuffle_entail_wit_14_2_split_goal_3.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_2_split_goal_4 : anti_shuffle_entail_wit_14_2_split_goal_4.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_2_split_goal_5 : anti_shuffle_entail_wit_14_2_split_goal_5.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_2_split_goal_6 : anti_shuffle_entail_wit_14_2_split_goal_6.
Proof.
Abort.

Lemma proof_of_anti_shuffle_entail_wit_14_2 : anti_shuffle_entail_wit_14_2.
Proof.
  left.
  pre_process.
  pose proof PreH19 as Hsafe_full.
  destruct PreH19 as [_ [_ [_ [_ [Hterminal _]]]]].
  assert (Hiend : i = string_length str_l + 1).
  { rewrite <- PreH4. lia. }
  pose proof (Hterminal i first out_l_2 cur_l PreH21 Hiend PreH13)
    as [Hcur_nil Hfinal].
  pose proof Hfinal as Hfinal_full.
  destruct Hfinal as [Hout_len Hspec].
  assert (Hcur_len0 : cur_len = 0).
  { rewrite Hcur_nil, Zlength_nil in PreH12. lia. }
  assert (Hout_len_n : out_len = n).
  { rewrite <- PreH11. rewrite PreH4. exact Hout_len. }
  assert (Hscan_end : anti_shuffle_scan_state_86 str_l (n + 1) first out_l_2 nil).
  { rewrite PreH4. rewrite <- Hiend. rewrite <- Hcur_nil. exact PreH21. }
  rewrite Hcur_nil.
  Exists out_l_2.
  entailer!.
  all: try exact Hsafe_full; try exact Hscan_end; try exact Hfinal_full;
       try exact Hout_len; try exact Hspec; try lia.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_15 : anti_shuffle_entail_wit_15.
Proof.
  left.
  pre_process.
  Exists out_l_2.
  replace cur_len with 0 by lia.
  rewrite (CharArray.full_empty cur 0).
  sep_apply (CharArray.undef_seg_to_undef_full cur 0 (n + 1)).
  replace (cur + 0 * 1) with cur by lia.
  replace (n + 1 - 0) with (n + 1) by lia.
  replace (cur + 0 * sizeof (CHAR)) with cur by lia.
  replace (out_len + 1) with (n + 1) by lia.
  rewrite (CharArray.undef_seg_empty out (n + 1)).
  unfold store_string.
  entailer!.
Qed.


Lemma proof_of_anti_shuffle_entail_wit_16 : anti_shuffle_entail_wit_16.
Proof.
  pre_process.
  Exists out_l_2.
  unfold store_string.
  entailer!.
Qed.


Lemma proof_of_anti_shuffle_return_wit_1 : anti_shuffle_return_wit_1.
Proof.
  left.
  pre_process.
  Exists out_l_2.
  replace (out_len + 1) with (string_length str_l + 1) by lia.
  entailer!.
Qed.


Lemma proof_of_anti_shuffle_partial_solve_wit_2_pure_split_goal_1 : anti_shuffle_partial_solve_wit_2_pure_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_2_pure : anti_shuffle_partial_solve_wit_2_pure.
Proof.
  left.
  pre_process; entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.


Lemma proof_of_anti_shuffle_partial_solve_wit_3_pure_split_goal_1 : anti_shuffle_partial_solve_wit_3_pure_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_3_pure : anti_shuffle_partial_solve_wit_3_pure.
Proof.
  left.
  pre_process; entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.


Lemma proof_of_anti_shuffle_partial_solve_wit_6_pure_split_goal_1 : anti_shuffle_partial_solve_wit_6_pure_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_6_pure : anti_shuffle_partial_solve_wit_6_pure.
Proof.
  left.
  pre_process.
  match goal with
  | H : anti_shuffle_scan_state_86 _ _ _ _ _ |- _ =>
      unfold anti_shuffle_scan_state_86 in H;
      destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]
  end.
  entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.


Lemma proof_of_anti_shuffle_partial_solve_wit_7_pure_split_goal_1 : anti_shuffle_partial_solve_wit_7_pure_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_7_pure : anti_shuffle_partial_solve_wit_7_pure.
Proof.
  left.
  pre_process.
  match goal with
  | H : anti_shuffle_scan_state_86 _ _ _ _ _ |- _ =>
      unfold anti_shuffle_scan_state_86 in H;
      destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]
  end.
  entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.


Lemma proof_of_anti_shuffle_partial_solve_wit_8_pure_split_goal_1 : anti_shuffle_partial_solve_wit_8_pure_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_8_pure : anti_shuffle_partial_solve_wit_8_pure.
Proof.
  left.
  pre_process.
  match goal with
  | H : anti_shuffle_scan_state_86 _ _ _ _ _ |- _ =>
      unfold anti_shuffle_scan_state_86 in H;
      destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]
  end.
  entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.


Lemma proof_of_anti_shuffle_partial_solve_wit_9_pure_split_goal_1 : anti_shuffle_partial_solve_wit_9_pure_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_9_pure : anti_shuffle_partial_solve_wit_9_pure.
Proof.
  left.
  pre_process.
  match goal with
  | H : anti_shuffle_scan_state_86 _ _ _ _ _ |- _ =>
      unfold anti_shuffle_scan_state_86 in H;
      destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]
  end.
  entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.


Lemma proof_of_anti_shuffle_partial_solve_wit_17_pure_split_goal_1 : anti_shuffle_partial_solve_wit_17_pure_split_goal_1.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_17_pure_split_goal_2 : anti_shuffle_partial_solve_wit_17_pure_split_goal_2.
Proof.
Abort.

Lemma proof_of_anti_shuffle_partial_solve_wit_17_pure : anti_shuffle_partial_solve_wit_17_pure.
Proof.
  left.
  pre_process; entailer!.
  all: unfold string_length in *; pose proof (Zlength_nonneg str_l); lia.
Qed.
