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
From SimpleC.EE Require Import C_143_goal.
From SimpleC.EE Require Import C_143_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.coins_143.
Local Open Scope sac.

Lemma split_c_string_143 : forall input sentence start i n,
  0 <= start <= i ->
  i <= n ->
  Zlength input = n ->
  CharArray.full sentence (string_length input + 1) (c_string input) |--
    CharArray.seg sentence 0 start (sublist 0 start (c_string input)) **
    CharArray.full (sentence + start * sizeof(CHAR)) (i - start)
      (sublist start i input) **
    CharArray.seg sentence i (n + 1) (sublist i (n + 1) (c_string input)).
Proof.
  intros input sentence start i n Hstart Hi Hlen.
  unfold string_length. rewrite Hlen.
  sep_apply CharArray.full_to_seg.
  assert (Hsplit1 : 0 <= start <= n + 1) by lia.
  pose proof (CharArray.seg_split_to_seg sentence 0 start (n + 1)
    (c_string input) Hsplit1) as HS1.
  sep_apply HS1.
  replace (start - 0) with start in * by lia.
  replace (n + 1 - 0) with (n + 1) in * by lia.
  assert (Hsplit2 : start <= i <= n + 1) by lia.
  pose proof (CharArray.seg_split_to_seg sentence start i (n + 1)
    (sublist start (n + 1) (c_string input)) Hsplit2) as HS2.
  sep_apply_l_atomic HS2.
  sep_apply_l_atomic (CharArray.seg_to_full sentence start i
    (sublist 0 (i - start) (sublist start (n + 1) (c_string input)))).
  repeat rewrite Zsublist_Zsublist by lia.
  rewrite sublist_c_string_prefix_143 by lia.
  replace (0 + start) with start by lia.
  replace (i - start + start) with i by lia.
  replace (n + 1 - start + start) with (n + 1) by lia.
  entailer!.
Qed.

Lemma merge_c_string_143 : forall input sentence start i n input_pre input_post,
  0 <= start <= i -> i <= n -> Zlength input = n ->
  input_pre = sublist 0 start (c_string input) ->
  input_post = sublist i (n + 1) (c_string input) ->
  CharArray.seg sentence 0 start input_pre **
  CharArray.full (sentence + start * sizeof(CHAR)) (i - start)
    (sublist start i input) **
  CharArray.seg sentence i (n + 1) input_post |--
  CharArray.full sentence (string_length input + 1) (c_string input).
Proof.
  intros input sentence start i n input_pre input_post Hstart Hi Hlen -> ->.
  sep_apply_l_atomic (CharArray.full_to_seg
    (sentence + start * sizeof(CHAR)) (i - start) (sublist start i input)).
  rewrite <- (CharArray.seg_0_shift sentence start i (sublist start i input)).
  pose proof (CharArray.seg_merge_to_seg sentence 0 start i
    (sublist 0 start (c_string input)) (sublist start i input) Hstart) as HM1.
  sep_apply_l_atomic HM1.
  assert (Hi' : 0 <= i <= n + 1) by lia.
  pose proof (CharArray.seg_merge_to_full sentence 0 i (n + 1)
    (List.app (sublist 0 start (c_string input)) (sublist start i input))
    (sublist i (n + 1) (c_string input)) Hi') as HM2.
  sep_apply_l_atomic HM2.
  unfold string_length. rewrite Hlen.
  rewrite <- (sublist_c_string_prefix_143 input start i Hstart ltac:(lia)).
  assert (Hclen : Zlength (c_string input) = n + 1).
  { unfold c_string. rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen. lia. }
  rewrite <- (sublist_split 0 i start (c_string input)) by lia.
  rewrite <- (sublist_split 0 (n + 1) i (c_string input)) by lia.
  assert (Hwhole : sublist 0 (n + 1) (c_string input) = c_string input).
  { rewrite <- Hclen.
    replace (c_string input) with (List.app (c_string input) (@nil Z)) at 2
      by apply app_nil_r.
    apply sublist_app_exact1. }
  rewrite Hwhole.
  replace (sentence + 0 * sizeof(CHAR)) with sentence by lia.
  replace (n + 1 - 0) with (n + 1) by lia.
  entailer!.
Qed.

Lemma merge_output_143 : forall out out_len l prefix word,
  0 <= out_len -> 0 <= l ->
  CharArray.full out out_len prefix **
  CharArray.full (out + out_len * sizeof(CHAR)) l word |--
  CharArray.full out (out_len + l) (List.app prefix word).
Proof.
  intros out out_len l prefix word Hout Hl.
  sep_apply_l_atomic (CharArray.full_to_seg out out_len prefix).
  sep_apply_l_atomic (CharArray.full_to_seg
    (out + out_len * sizeof(CHAR)) l word).
  pose proof (CharArray.seg_0_shift out out_len (out_len + l) word) as Hshift.
  replace (out_len + l - out_len) with l in Hshift by lia.
  rewrite <- Hshift.
  assert (Hb : 0 <= out_len <= out_len + l) by lia.
  pose proof (CharArray.seg_merge_to_full out 0 out_len (out_len + l)
    prefix word Hb) as HM.
  sep_apply_l_atomic HM.
  replace (out_len + l - 0) with (out_len + l) by lia.
  replace (out + 0 * sizeof(CHAR)) with out by lia.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_safety_wit_1 : words_in_sentence_safety_wit_1.
Proof.
  unfold words_in_sentence_safety_wit_1. right. intros.
  pose proof (problem_143_pre_z_length _ PreH4) as [Hlo Hhi].
  unfold string_length in PreH1 |- *. entailer!.
Qed.

Lemma proof_of_words_in_sentence_safety_wit_26 : words_in_sentence_safety_wit_26.
Proof. unfold words_in_sentence_safety_wit_26; right; intros; entailer!. Qed.

Lemma proof_of_words_in_sentence_safety_wit_34 : words_in_sentence_safety_wit_34.
Proof.
  unfold words_in_sentence_safety_wit_34; right; intros.
  match goal with H : problem_143_pre_z _ |- _ =>
    pose proof (problem_143_pre_z_length _ H) as [Hlo Hhi]
  end.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_words_in_sentence_safety_wit_42 : words_in_sentence_safety_wit_42.
Proof.
  unfold words_in_sentence_safety_wit_42; right; intros.
  match goal with H : problem_143_pre_z _ |- _ =>
    pose proof (problem_143_pre_z_length _ H) as [Hlo Hhi]
  end.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_words_in_sentence_safety_wit_43 : words_in_sentence_safety_wit_43.
Proof.
  unfold words_in_sentence_safety_wit_43; right; intros.
  match goal with H : problem_143_pre_z _ |- _ =>
    pose proof (problem_143_pre_z_length _ H) as [Hlo Hhi]
  end.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_words_in_sentence_safety_wit_44 : words_in_sentence_safety_wit_44.
Proof.
  unfold words_in_sentence_safety_wit_44; right; intros.
  match goal with H : problem_143_pre_z _ |- _ =>
    pose proof (problem_143_pre_z_length _ H) as [Hlo Hhi]
  end.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_1 : words_in_sentence_entail_wit_1.
Proof.
  unfold words_in_sentence_entail_wit_1. right. intros.
  pose proof (problem_143_pre_z_length _ PreH5) as [Hlo Hhi].
  Exists (@nil (list Z)) (@nil Z) (@nil (list Z)).
  unfold string_length in PreH2 |- *.
  assert (Hmin : min_z_143 0 retval = 0) by
    (unfold min_z_143; apply Z.min_l; lia).
  assert (Hprefix : SentencePrefix143 input 0 (@nil Z) (@nil (list Z))).
  { unfold SentencePrefix143, SpaceFreeZ143. left. cbn.
    split; [reflexivity|].
    repeat constructor. intros Hin; inversion Hin. }
  assert (Hprime : PrimeLengthWordsZ143 (@nil (list Z)) (@nil (list Z))) by constructor.
  assert (Hcur : current_word_143 input 0 (-1) (@nil Z)).
  { unfold current_word_143. left; auto. }
  assert (Hgap : output_gap_outer_143 0 (-1) 0).
  { unfold output_gap_outer_143. auto. }
  assert (Hdone : outer_done_143 0 retval (-1)).
  { unfold outer_done_143. left. lia. }
  subst sentence_addr.
  rewrite Hmin.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_2_1 : words_in_sentence_entail_wit_2_1.
Proof.
  unfold words_in_sentence_entail_wit_2_1. right. intros.
  unfold min_z_143 in *. replace (Z.min i n) with i in * by lia.
  pose proof (current_word_active_143 _ _ _ _ PreH24 ltac:(lia)) as Hcur.
  pose proof (problem_143_pre_z_length _ PreH26) as [Hlo Hhi].
  unfold string_length in PreH25.
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len)
    by (rewrite <- PreH23; exact PreH20).
  assert (Hgap : output_gap_inner_143 out_len start).
  { unfold output_gap_outer_143 in PreH11.
    unfold output_gap_inner_143. destruct PreH11 as [_ [Hs|[Hz|Hg]]]; lia. }
  assert (Hboundary : word_boundary_143 input i n).
  { unfold word_boundary_143. left. lia. }
  Exists selected_2 cur_2 words_2. entailer!.
  apply prime_scan_init_false_143; lia.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_2_2 : words_in_sentence_entail_wit_2_2.
Proof.
  unfold words_in_sentence_entail_wit_2_2. right. intros.
  unfold min_z_143 in *. replace (Z.min i n) with i in * by lia.
  pose proof (current_word_active_143 _ _ _ _ PreH25 ltac:(lia)) as Hcur.
  pose proof (problem_143_pre_z_length _ PreH27) as [Hlo Hhi].
  unfold string_length in PreH26.
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len)
    by (rewrite <- PreH24; exact PreH21).
  assert (Hgap : output_gap_inner_143 out_len start).
  { unfold output_gap_outer_143 in PreH12.
    unfold output_gap_inner_143. destruct PreH12 as [_ [Hs|[Hz|Hg]]]; lia. }
  assert (Hboundary : word_boundary_143 input i n).
  { unfold word_boundary_143. right. auto. }
  Exists selected_2 cur_2 words_2. entailer!.
  apply prime_scan_init_false_143; lia.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_2_3 : words_in_sentence_entail_wit_2_3.
Proof.
  unfold words_in_sentence_entail_wit_2_3. right. intros.
  unfold min_z_143 in *. replace (Z.min i n) with i in * by lia.
  pose proof (current_word_active_143 _ _ _ _ PreH24 ltac:(lia)) as Hcur.
  pose proof (problem_143_pre_z_length _ PreH26) as [Hlo Hhi].
  unfold string_length in PreH25.
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len)
    by (rewrite <- PreH23; exact PreH20).
  assert (Hgap : output_gap_inner_143 out_len start).
  { unfold output_gap_outer_143 in PreH11.
    unfold output_gap_inner_143. destruct PreH11 as [_ [Hs|[Hz|Hg]]]; lia. }
  assert (Hboundary : word_boundary_143 input i n).
  { unfold word_boundary_143. left. lia. }
  Exists selected_2 cur_2 words_2. entailer!.
  apply prime_scan_init_true_143; lia.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_2_4 : words_in_sentence_entail_wit_2_4.
Proof.
  unfold words_in_sentence_entail_wit_2_4. right. intros.
  unfold min_z_143 in *. replace (Z.min i n) with i in * by lia.
  pose proof (current_word_active_143 _ _ _ _ PreH25 ltac:(lia)) as Hcur.
  pose proof (problem_143_pre_z_length _ PreH27) as [Hlo Hhi].
  unfold string_length in PreH26.
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len)
    by (rewrite <- PreH24; exact PreH21).
  assert (Hgap : output_gap_inner_143 out_len start).
  { unfold output_gap_outer_143 in PreH12.
    unfold output_gap_inner_143. destruct PreH12 as [_ [Hs|[Hz|Hg]]]; lia. }
  assert (Hboundary : word_boundary_143 input i n).
  { unfold word_boundary_143. right. auto. }
  Exists selected_2 cur_2 words_2. entailer!.
  apply prime_scan_init_true_143; lia.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_3_1 : words_in_sentence_entail_wit_3_1.
Proof.
  unfold words_in_sentence_entail_wit_3_1. right. intros.
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len)
    by (rewrite <- PreH23; exact PreH20).
  Exists selected_2 cur_2 words_2. entailer!.
  eapply prime_scan_step_zero_143; eauto.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_3_2 : words_in_sentence_entail_wit_3_2.
Proof.
  unfold words_in_sentence_entail_wit_3_2. right. intros.
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len)
    by (rewrite <- PreH23; exact PreH20).
  Exists selected_2 cur_2 words_2. entailer!.
  eapply prime_scan_step_nonzero_143; eauto.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_4_1 : words_in_sentence_entail_wit_4_1.
Proof.
  unfold words_in_sentence_entail_wit_4_1. right. intros.
  assert (out_len = 0) by lia. subst out_len.
  match goal with HZ : Zlength output_l = 0 |- _ => rewrite HZ in * end.
  assert (Hlen : Zlength input = n).
  { unfold string_length in PreH26. lia. }
  assert (Hascii : all_ascii (sublist start i input)).
  { apply valid_string_sublist_ascii_143; auto; lia. }
  assert (Hwordlen : Zlength (sublist start i input) = l).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hcopy : copy_prefix_143 (join_words_z_143 selected_2) output_l).
  { assert (Hnil : output_l = (@nil Z)).
    { destruct output_l as [|a output_l]; [reflexivity|].
      match goal with HZ : Zlength (a :: output_l) = 0 |- _ =>
        rewrite Zlength_cons in HZ; pose proof (Zlength_nonneg output_l); lia
      end. }
    assert (Hjoin : join_words_z_143 selected_2 = (@nil Z)) by
        (rewrite <- PreH23; exact Hnil).
    subst output_l. unfold copy_prefix_143. rewrite Hjoin. auto. }
  assert (Hgap : output_gap_copy_143 0 start).
  { unfold output_gap_inner_143 in PreH17.
    unfold output_gap_copy_143. lia. }
  pose proof (CharArray.undef_seg_split_to_undef_seg out 0 l (n + 1)) as HU.
  assert (Hb : 0 <= l <= n + 1) by lia.
  specialize (HU Hb).
  sep_apply_l_atomic HU.
  sep_apply_l_atomic (CharArray.undef_seg_to_undef_full out 0 l).
  pose proof (split_c_string_143 input sentence_addr start i n ltac:(lia) ltac:(lia) Hlen) as HS.
  sep_apply_l_atomic HS.
  Exists selected_2 cur_2 words_2.
  replace (i - start) with l by lia.
  replace (l - 0) with l by lia.
  replace (0 + l) with l by lia.
  replace (out + 0 * sizeof(CHAR)) with out by lia.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_4_2 : words_in_sentence_entail_wit_4_2.
Proof.
  unfold words_in_sentence_entail_wit_4_2. right. intros.
  assert (Hlen : Zlength input = n).
  { unfold string_length in PreH26. lia. }
  assert (Hascii : all_ascii (sublist start i input)).
  { apply valid_string_sublist_ascii_143; auto; lia. }
  assert (Hwordlen : Zlength (sublist start i input) = l).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hgap : output_gap_copy_143 (out_len + 1) start).
  { unfold output_gap_inner_143 in PreH17.
    unfold output_gap_copy_143. lia. }
  assert (Htotal : out_len + 1 + l <= n).
  { unfold output_gap_inner_143 in PreH17. lia. }
  assert (Hcopy : copy_prefix_143 (join_words_z_143 selected_2)
                                  (output_l ++ (32 :: nil))).
  { unfold copy_prefix_143. right. split.
    - intro Hnil. rewrite PreH23 in PreH20.
      rewrite Hnil, Zlength_nil in PreH20. lia.
    - rewrite <- PreH23. reflexivity. }
  pose proof (CharArray.undef_seg_split_to_undef_seg
                out (out_len + 1) ((out_len + 1) + l) (n + 1)) as HU.
  assert (Hb : out_len + 1 <= out_len + 1 + l <= n + 1) by
      (unfold output_gap_inner_143 in PreH17; lia).
  specialize (HU Hb).
  sep_apply_l_atomic HU.
  sep_apply_l_atomic
    (CharArray.undef_seg_to_undef_full out (out_len + 1) ((out_len + 1) + l)).
  pose proof (split_c_string_143 input sentence_addr start i n ltac:(lia) ltac:(lia) Hlen) as HS.
  sep_apply_l_atomic HS.
  Exists selected_2 cur_2 words_2.
  replace (i - start) with l by lia.
  replace (out_len + 1 + l - (out_len + 1)) with l by lia.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_5_1 : words_in_sentence_entail_wit_5_1.
Proof.
  unfold words_in_sentence_entail_wit_5_1. right. intros.
  unfold string_length in PreH25.
  unfold min_z_143 in *. replace (Z.min i n) with i in * by lia.
  replace (Z.min (i + 1) n) with (i + 1) in * by lia.
  unfold current_word_143 in PreH24.
  destruct PreH24 as [[Hstart Hcur]|Hbad]; [|lia]. subst start cur_2.
  pose proof (sentence_prefix_char_143 input i (@nil Z) words_2
                (Znth i (c_string input) 0) ltac:(lia) PreH28 PreH21
                eq_refl PreH3) as Hsent.
  pose proof (current_word_start_char_143 input i (@nil Z)
                (Znth i (c_string input) 0) ltac:(lia)
                (current_word_finished_143 input i) eq_refl PreH3) as Hcur.
  assert (Hgap : output_gap_outer_143 out_len i (i + 1)).
  { unfold output_gap_outer_143 in *. destruct PreH11 as [[Hz|Hg] _].
    - subst out_len. auto.
    - split; [right; lia|right; right; lia]. }
  assert (Hdone : outer_done_143 (i + 1) n i).
  { unfold outer_done_143. left. lia. }
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len) by
      (rewrite <- PreH23; exact PreH20).
  Exists selected_2 (Znth i (c_string input) 0 :: nil) words_2.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_5_2 : words_in_sentence_entail_wit_5_2.
Proof.
  unfold words_in_sentence_entail_wit_5_2. right. intros.
  unfold string_length in PreH25.
  unfold min_z_143 in *. replace (Z.min i n) with i in * by lia.
  replace (Z.min (i + 1) n) with (i + 1) in * by lia.
  pose proof (sentence_prefix_char_143 input i cur_2 words_2
                (Znth i (c_string input) 0) ltac:(lia) PreH28 PreH21
                eq_refl PreH3) as Hsent.
  pose proof (current_word_extend_char_143 input i start cur_2
                (Znth i (c_string input) 0) ltac:(lia) PreH28 ltac:(lia)
                PreH24 eq_refl PreH3) as Hcur.
  assert (Hgap : output_gap_outer_143 out_len start (i + 1)).
  { unfold output_gap_outer_143 in *. destruct PreH11 as [[Hz|Hg] Hs].
    - subst out_len. auto.
    - split; [right; lia|exact Hs]. }
  assert (Hdone : outer_done_143 (i + 1) n start).
  { unfold outer_done_143. left. lia. }
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len) by
      (rewrite <- PreH23; exact PreH20).
  Exists selected_2 (List.app cur_2 (Znth i (c_string input) 0 :: nil)) words_2.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_5_3 : words_in_sentence_entail_wit_5_3.
Proof.
  unfold words_in_sentence_entail_wit_5_3. right. intros.
  unfold string_length in PreH20.
  pose proof (current_word_active_143 _ _ _ _ PreH27 PreH6) as
      [Hbounds [Hcur [Hcurlen Hfree]]].
  assert (Hcurl : Zlength cur_2 = l) by (rewrite Hcur; exact PreH2).
  assert (Hprimeval : IsPrime (Z.to_nat (Zlength cur_2))).
  { rewrite Hcurl.
    apply (proj1 (prime_scan_done_143 l j isp ltac:(lia) PreH14 PreH28)).
    exact PreH13. }
  assert (Hprime : PrimeLengthWordsZ143
      (List.app words_2 (cur_2 :: nil))
      (List.app selected_2 (cur_2 :: nil))).
  { apply prime_words_keep_snoc_143; assumption. }
  assert (Hcopied : List.app output_pre cur_2 =
      join_words_z_143 (List.app selected_2 (cur_2 :: nil))).
  { eapply copied_prime_output_143; eauto. }
  assert (Hsent : SentencePrefix143 input (Z.min (i + 1) n) (@nil Z)
                    (List.app words_2 (cur_2 :: nil))).
  { unfold word_boundary_143 in PreH12. destruct PreH12 as [->|[Hlt Hspace]].
    - rewrite Z.min_r by lia. rewrite PreH20 in *.
      apply sentence_prefix_finish_end_143 with (start := start); auto.
    - rewrite Z.min_l by lia.
      apply sentence_prefix_finish_space_143; auto; lia. }
  assert (Hgap : output_gap_outer_143 (out_len + l) (-1) (i + 1)).
  { unfold output_gap_copy_143 in PreH11.
    unfold output_gap_outer_143. split; [right; destruct PreH11; lia|left; lia]. }
  assert (Hdone : outer_done_143 (i + 1) n (-1)).
  { unfold outer_done_143. right. reflexivity. }
  assert (Houterbound : out_len + l <= i + 1).
  { unfold output_gap_copy_143 in PreH11. destruct PreH11; lia. }
  assert (Houtlen : Zlength (List.app output_pre cur_2) = out_len + l).
  { rewrite Zlength_app, PreH30, Hcurlen. lia. }
  pose proof (current_word_finished_143 input (Z.min (i + 1) n)) as HcurFinal.
  pose proof (merge_output_143 out out_len l output_pre
                (sublist start i input) PreH9 PreH4) as HMO.
  sep_apply_l_atomic HMO.
  assert (Hlen : Zlength input = n) by lia.
  pose proof (merge_c_string_143 input sentence_addr start i n input_pre input_post
                ltac:(lia) PreH8 Hlen PreH31 PreH32) as HMS.
  replace (i - start) with l in HMS by lia.
  sep_apply_l_atomic HMS.
  Exists (List.app selected_2 (cur_2 :: nil)) (@nil Z)
         (List.app words_2 (cur_2 :: nil)).
  rewrite <- Hcur in *.
  rewrite <- Hcopied.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_5_4 : words_in_sentence_entail_wit_5_4.
Proof.
  unfold words_in_sentence_entail_wit_5_4. right. intros.
  unfold string_length in PreH25.
  pose proof (current_word_active_143 _ _ _ _ PreH23 ltac:(lia)) as
      [Hbounds [Hcur [Hcurlen Hfree]]].
  assert (Hnotprime : ~ IsPrime (Z.to_nat (Zlength cur_2))).
  { rewrite Hcurlen. replace (i - start) with l by lia.
    pose proof (prime_scan_done_143 l j isp ltac:(lia) PreH2 PreH24) as [_ Hback].
    intro Hp. specialize (Hback Hp). lia. }
  assert (Hprime : PrimeLengthWordsZ143
      (List.app words_2 (cur_2 :: nil)) selected_2).
  { apply prime_words_drop_snoc_143; assumption. }
  assert (Hsent : SentencePrefix143 input (Z.min (i + 1) n) (@nil Z)
                    (List.app words_2 (cur_2 :: nil))).
  { unfold word_boundary_143 in PreH17. destruct PreH17 as [->|[Hlt Hspace]].
    - rewrite Z.min_r by lia.
      rewrite PreH25 in *.
      apply sentence_prefix_finish_end_143 with (start := start); auto.
    - rewrite Z.min_l by lia.
      apply sentence_prefix_finish_space_143; auto; lia. }
  assert (Hgap : output_gap_outer_143 out_len (-1) (i + 1)).
  { unfold output_gap_inner_143 in PreH16.
    unfold output_gap_outer_143. split; [destruct PreH16; auto; right; lia|left; lia]. }
  assert (Hdone : outer_done_143 (i + 1) n (-1)).
  { unfold outer_done_143. right. reflexivity. }
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len) by
      (rewrite <- PreH22; exact PreH19).
  pose proof (current_word_finished_143 input (Z.min (i + 1) n)) as HcurFinal.
  Exists selected_2 (@nil Z) (List.app words_2 (cur_2 :: nil)).
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_5_5 : words_in_sentence_entail_wit_5_5.
Proof.
  unfold words_in_sentence_entail_wit_5_5. right. intros.
  unfold string_length in PreH24.
  unfold min_z_143 in *. replace (Z.min i n) with n in * by lia.
  replace (Z.min (i + 1) n) with n in * by lia.
  assert (i = n) by lia. subst i.
  unfold current_word_143 in PreH23.
  destruct PreH23 as [[Hstart Hcur]|Hbad]; [|lia]. subst start cur_2.
  assert (Hgap : output_gap_outer_143 out_len (-1) (n + 1)).
  { unfold output_gap_outer_143 in *. destruct PreH10 as [Hg _].
    split; [destruct Hg; auto; right; lia|left; lia]. }
  assert (Hdone : outer_done_143 (n + 1) n (-1)).
  { unfold outer_done_143. right. reflexivity. }
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len) by
      (rewrite <- PreH22; exact PreH19).
  pose proof (current_word_finished_143 input n) as HcurFinal.
  Exists selected_2 (@nil Z) words_2.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_5_6 : words_in_sentence_entail_wit_5_6.
Proof.
  unfold words_in_sentence_entail_wit_5_6. right. intros.
  unfold string_length in PreH25.
  unfold min_z_143 in *. replace (Z.min i n) with i in * by lia.
  replace (Z.min (i + 1) n) with (i + 1) in * by lia.
  unfold current_word_143 in PreH24.
  destruct PreH24 as [[Hstart Hcur]|Hbad]; [|lia]. subst start cur_2.
  pose proof (sentence_prefix_finish_space_143 input i (@nil Z) words_2
                ltac:(lia) PreH28 PreH21 PreH3) as Hsent.
  assert (Hprime : PrimeLengthWordsZ143
      (List.app words_2 ((@nil Z) :: nil)) selected_2).
  { apply prime_words_drop_snoc_143; [exact PreH22|].
    unfold IsPrime. intros [Htwo _]. simpl in Htwo. lia. }
  assert (Hgap : output_gap_outer_143 out_len (-1) (i + 1)).
  { unfold output_gap_outer_143 in *. destruct PreH11 as [Hg _].
    split; [destruct Hg; auto; right; lia|left; lia]. }
  assert (Hdone : outer_done_143 (i + 1) n (-1)).
  { unfold outer_done_143. right. reflexivity. }
  assert (Hout : Zlength (join_words_z_143 selected_2) = out_len) by
      (rewrite <- PreH23; exact PreH20).
  pose proof (current_word_finished_143 input (i + 1)) as HcurFinal.
  Exists selected_2 (@nil Z) (List.app words_2 ((@nil Z) :: nil)).
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_return_wit_1 : words_in_sentence_return_wit_1.
Proof.
  unfold words_in_sentence_return_wit_1. right. intros.
  assert (i = n + 1) by lia. subst i.
  unfold outer_done_143 in PreH10.
  destruct PreH10 as [Hbad|Hstart]; [lia|].
  unfold min_z_143 in *; replace (Z.min (n + 1) n) with n in * by lia.
  unfold current_word_143 in PreH22.
  destruct PreH22 as [[_ Hcur]|Hactive]; [|lia]. subst cur start.
  assert (Hlen : Zlength input = n).
  { unfold string_length in PreH23. lia. }
  assert (Hspec : problem_143_spec_z input output_l).
  { apply (final_spec_z_143 input words selected output_l PreH25).
    - rewrite Hlen. exact PreH19.
    - exact PreH20.
    - exact PreH21. }
  Exists output_l.
  unfold string_length, c_string in *.
  rewrite PreH18, Hlen.
  entailer!.
Qed.

Lemma proof_of_words_in_sentence_partial_solve_wit_1_pure : words_in_sentence_partial_solve_wit_1_pure.
Proof.
  unfold words_in_sentence_partial_solve_wit_1_pure. right. intros.
  pose proof (problem_143_pre_z_length _ PreH3) as [Hlo Hhi].
  unfold string_length; entailer!.
Qed.

Lemma proof_of_words_in_sentence_partial_solve_wit_2_pure : words_in_sentence_partial_solve_wit_2_pure.
Proof.
  unfold words_in_sentence_partial_solve_wit_2_pure. right. intros.
  pose proof (problem_143_pre_z_length _ PreH6) as [Hlo Hhi].
  unfold string_length in *; entailer!.
Qed.
