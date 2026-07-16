Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
From SimpleC.StdLib Require Import string_lib.
Import ListNotations.

Load "../spec/143".

Local Open Scope Z_scope.

Definition ascii_of_z_143 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Definition string_of_list_z_143 (l : list Z) : string :=
  string_of_list_ascii (map ascii_of_z_143 l).

Definition ascii_range_z_143 (l : list Z) : Prop :=
  Forall (fun z => 0 <= z <= 127) l.

Definition problem_143_pre_z (input : list Z) : Prop :=
  problem_143_pre (string_of_list_z_143 input).

Definition problem_143_spec_z (input output : list Z) : Prop :=
  problem_143_spec
    (string_of_list_z_143 input)
    (string_of_list_z_143 output).

Lemma problem_143_pre_z_length : forall input,
  problem_143_pre_z input ->
  1 <= Zlength input <= 100.
Proof.
  intros input Hpre.
  unfold problem_143_pre_z, problem_143_pre, string_of_list_z_143 in Hpre.
  rewrite list_ascii_of_string_of_list_ascii in Hpre.
  destruct Hpre as [Hlo [Hhi _]].
  rewrite !map_length in Hlo, Hhi.
  rewrite Zlength_correct.
  split.
  - exact (proj1 (Nat2Z.inj_le 1 (List.length input)) Hlo).
  - exact (proj1 (Nat2Z.inj_le (List.length input) 100) Hhi).
Qed.

Lemma valid_string_sublist_ascii_143 : forall input lo hi,
  valid_string input ->
  0 <= lo <= hi ->
  hi <= Zlength input ->
  all_ascii (sublist lo hi input).
Proof.
  intros input lo hi [Hall _] Hbounds Hhi k Hk.
  rewrite Zlength_sublist in Hk by lia.
  rewrite Znth_sublist by lia.
  apply Hall. lia.
Qed.

Lemma sublist_c_string_prefix_143 : forall input lo hi,
  0 <= lo <= hi ->
  hi <= Zlength input ->
  sublist lo hi (c_string input) = sublist lo hi input.
Proof.
  intros. unfold c_string.
  apply sublist_split_app_l; lia.
Qed.

Definition SpaceFreeZ143 (word : list Z) : Prop :=
  ~ In 32 word.

Fixpoint join_words_z_143 (words : list (list Z)) : list Z :=
  match words with
  | [] => []
  | [word] => word
  | word :: rest => word ++ 32 :: join_words_z_143 rest
  end.

Definition copy_prefix_143 (old prefix : list Z) : Prop :=
  (old = [] /\ prefix = []) \/
  (old <> [] /\ prefix = List.app old [32]).

Inductive PrimeLengthWordsZ143 : list (list Z) -> list (list Z) -> Prop :=
| prime_words_z_nil :
    PrimeLengthWordsZ143 [] []
| prime_words_z_keep : forall word words selected,
    IsPrime (Z.to_nat (Zlength word)) ->
    PrimeLengthWordsZ143 words selected ->
    PrimeLengthWordsZ143 (word :: words) (word :: selected)
| prime_words_z_drop : forall word words selected,
    ~ IsPrime (Z.to_nat (Zlength word)) ->
    PrimeLengthWordsZ143 words selected ->
    PrimeLengthWordsZ143 (word :: words) selected.

Definition SentencePrefix143
    (input : list Z) (i : Z) (cur : list Z) (words : list (list Z)) : Prop :=
  (sublist 0 i input = join_words_z_143 (words ++ [cur]) /\
   Forall SpaceFreeZ143 (words ++ [cur])) \/
  (i = Zlength input /\ cur = [] /\
   sublist 0 i input = join_words_z_143 words /\
   Forall SpaceFreeZ143 words).

Definition min_z_143 (x y : Z) : Z := Z.min x y.

Definition current_word_143
    (input : list Z) (i start : Z) (cur : list Z) : Prop :=
  (start = -1 /\ cur = []) \/
  (0 <= start < i /\
   cur = sublist start i input /\
   Zlength cur = i - start /\
   SpaceFreeZ143 cur).

Definition output_gap_outer_143 (out_len start i : Z) : Prop :=
  (out_len = 0 \/ out_len < i) /\
  (start < 0 \/ out_len = 0 \/ out_len < start).

Definition output_gap_inner_143 (out_len start : Z) : Prop :=
  out_len = 0 \/ out_len < start.

Definition output_gap_copy_143 (out_len start : Z) : Prop :=
  out_len = 0 \/ out_len <= start.

Definition word_boundary_143 (input : list Z) (i n : Z) : Prop :=
  i = n \/ (i < n /\ Znth i (c_string input) 0 = 32).

Definition outer_done_143 (i n start : Z) : Prop :=
  i <= n \/ start = -1.

Definition prime_scan_state_143 (l j isp : Z) : Prop :=
  2 <= j /\
  (j = 2 \/ (j - 1) * (j - 1) <= l) /\
  ((isp <> 0 /\
    2 <= l /\
    forall d, 2 <= d < j -> Z.rem l d <> 0) \/
   (isp = 0 /\
    (l < 2 \/ exists d, 2 <= d < j /\ Z.rem l d = 0))).

Lemma prime_scan_init_false_143 : forall l,
  0 < l < 2 -> prime_scan_state_143 l 2 0.
Proof.
  intros l Hl. unfold prime_scan_state_143.
  split; [lia|]. split; [left; reflexivity|].
  right. split; [reflexivity|]. left; lia.
Qed.

Lemma prime_scan_init_true_143 : forall l,
  2 <= l -> prime_scan_state_143 l 2 1.
Proof.
  intros l Hl. unfold prime_scan_state_143.
  split; [lia|]. split; [left; reflexivity|].
  left. split; [lia|]. split; [lia|].
  intros d Hd. lia.
Qed.

Lemma prime_scan_step_zero_143 : forall l j isp,
  prime_scan_state_143 l j isp ->
  j * j <= l ->
  Z.rem l j = 0 ->
  prime_scan_state_143 l (j + 1) 0.
Proof.
  intros l j isp Hstate Hsquare Hrem.
  unfold prime_scan_state_143 in *.
  destruct Hstate as [Hj [_ Hstate]].
  split; [lia|]. split; [right; replace (j + 1 - 1) with j by lia; exact Hsquare|].
  right. split; [reflexivity|].
  right. exists j. split; [lia|exact Hrem].
Qed.

Lemma prime_scan_step_nonzero_143 : forall l j isp,
  prime_scan_state_143 l j isp ->
  j * j <= l ->
  Z.rem l j <> 0 ->
  prime_scan_state_143 l (j + 1) isp.
Proof.
  intros l j isp Hstate Hsquare Hrem.
  unfold prime_scan_state_143 in *.
  destruct Hstate as [Hj [_ [[Hisp [Hl Hnone]] | [Hisp Hbad]]]].
  - split; [lia|]. split; [right; replace (j + 1 - 1) with j by lia; exact Hsquare|].
    left. repeat split; try assumption.
    intros d Hd. destruct (Z.eq_dec d j) as [->|Hne]; [exact Hrem|].
    apply Hnone. lia.
  - split; [lia|]. split; [right; replace (j + 1 - 1) with j by lia; exact Hsquare|].
    right. split; [exact Hisp|].
    destruct Hbad as [Hsmall | [d [Hd Hdiv]]].
    + left; exact Hsmall.
    + right. exists d. split; [lia|exact Hdiv].
Qed.

Lemma prime_scan_done_143 : forall l j isp,
  0 < l ->
  j * j > l ->
  prime_scan_state_143 l j isp ->
  (isp <> 0 <-> IsPrime (Z.to_nat l)).
Proof.
  intros l j isp Hl Hdone Hstate.
  unfold prime_scan_state_143 in Hstate.
  destruct Hstate as [Hj [Hreach Hstate]].
  split.
  - intros Hisp.
    destruct Hstate as [[_ [Hl2 Hnone]] | [Hzero _]]; [|contradiction].
    unfold IsPrime. split.
    + apply (proj1 (Z2Nat.inj_le 2 l ltac:(lia) ltac:(lia))); lia.
    + intros d Hd Hsquare Hmod.
      set (dz := Z.of_nat d).
      assert (Hdz : 2 <= dz) by (subst dz; lia).
      assert (Hdzsq : dz * dz <= l).
      { subst dz.
        apply (proj1 (Nat2Z.inj_le _ _)) in Hsquare.
        rewrite Nat2Z.inj_mul in Hsquare.
        rewrite Z2Nat.id in Hsquare by lia.
        exact Hsquare. }
      assert (Hdj : dz < j).
      { destruct (Z_lt_ge_dec dz j) as [Hlt|Hge]; [exact Hlt|].
        assert (j * j <= dz * dz).
        { apply Z.mul_le_mono_nonneg; lia. }
        lia. }
      specialize (Hnone dz ltac:(lia)).
      apply Hnone.
      assert (Hremmod : Z.rem l dz = l mod dz).
      { rewrite Z.rem_mod by lia.
        rewrite Z.sgn_pos by lia.
        rewrite !Z.abs_eq by lia.
        destruct (l mod dz); reflexivity. }
      rewrite Hremmod.
      apply (Z2Nat.inj (l mod dz) 0).
      * apply Z.mod_pos_bound; lia.
      * lia.
      * rewrite Z2Nat.inj_mod by lia.
        subst dz. rewrite Nat2Z.id. exact Hmod.
  - intros Hprime Hzero.
    destruct Hstate as [[Hnz _] | [_ Hbad]]; [contradiction|].
    unfold IsPrime in Hprime. destruct Hprime as [Htwo Hprime].
    destruct Hbad as [Hsmall | [d [[Hd2 Hdj] Hrem]]].
    + apply (proj2 (Z2Nat.inj_le 2 l ltac:(lia) ltac:(lia))) in Htwo.
      lia.
    + assert (Hdnonneg : 0 <= d) by lia.
      assert (Hdsquare : d * d <= l).
      { destruct Hreach as [-> | Hreach]; [lia|].
        assert (d * d <= (j - 1) * (j - 1)).
        { apply Z.mul_le_mono_nonneg; lia. }
        lia. }
      specialize (Hprime (Z.to_nat d)).
      assert (HmodZ : l mod d = 0).
      { assert (Hremmod : Z.rem l d = l mod d).
        { rewrite Z.rem_mod by lia.
          rewrite Z.sgn_pos by lia.
          rewrite !Z.abs_eq by lia.
          destruct (l mod d); reflexivity. }
        rewrite Hremmod in Hrem. exact Hrem. }
      apply Hprime.
      * apply (proj1 (Z2Nat.inj_le 2 d ltac:(lia) ltac:(lia))); lia.
      * pose proof (proj1 (Z2Nat.inj_le (d * d) l
          ltac:(apply Z.mul_nonneg_nonneg; lia) ltac:(lia)) Hdsquare) as Hnat.
        rewrite Z2Nat.inj_mul in Hnat by lia. exact Hnat.
      * rewrite <- Z2Nat.inj_mod by lia.
        rewrite HmodZ. reflexivity.
Qed.

Lemma current_word_active_143 : forall input i start cur,
  current_word_143 input i start cur ->
  0 <= start ->
  0 <= start < i /\
  cur = sublist start i input /\
  Zlength cur = i - start /\
  SpaceFreeZ143 cur.
Proof.
  intros input i start cur Hcur Hstart.
  unfold current_word_143 in Hcur.
  destruct Hcur as [[Hneg _] | Hactive]; [lia|exact Hactive].
Qed.

Lemma join_words_snoc_143 : forall words word,
  join_words_z_143 (words ++ [word]) =
  match words with
  | [] => word
  | _ => List.app (join_words_z_143 words) (32 :: word)
  end.
Proof.
  induction words as [|a words IH]; intros word; [reflexivity|].
  destruct words as [|b words].
  - reflexivity.
  - simpl in *. rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

Lemma join_words_extend_last_143 : forall words cur ch,
  join_words_z_143 (words ++ [List.app cur [ch]]) =
  List.app (join_words_z_143 (words ++ [cur])) [ch].
Proof.
  intros words cur ch. rewrite !join_words_snoc_143.
  destruct words; simpl; [reflexivity|].
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma join_words_finish_space_143 : forall words cur,
  join_words_z_143 ((words ++ [cur]) ++ [[]]) =
  List.app (join_words_z_143 (words ++ [cur])) [32].
Proof.
  intros words cur. rewrite join_words_snoc_143.
  destruct (List.app words [cur]) eqn:Heq; [|reflexivity].
  apply app_eq_nil in Heq. destruct Heq as [_ Hbad]. discriminate.
Qed.

Lemma prime_words_keep_snoc_143 : forall words selected word,
  PrimeLengthWordsZ143 words selected ->
  IsPrime (Z.to_nat (Zlength word)) ->
  PrimeLengthWordsZ143 (words ++ [word]) (selected ++ [word]).
Proof.
  intros words selected word Hrel Hprime.
  induction Hrel; simpl.
  - constructor; [exact Hprime|constructor].
  - constructor; auto.
  - apply prime_words_z_drop; auto.
Qed.

Lemma prime_words_drop_snoc_143 : forall words selected word,
  PrimeLengthWordsZ143 words selected ->
  ~ IsPrime (Z.to_nat (Zlength word)) ->
  PrimeLengthWordsZ143 (words ++ [word]) selected.
Proof.
  intros words selected word Hrel Hprime.
  induction Hrel; simpl.
  - constructor; [exact Hprime|constructor].
  - constructor; auto.
  - apply prime_words_z_drop; auto.
Qed.

Lemma space_free_extend_143 : forall cur ch,
  SpaceFreeZ143 cur -> ch <> 32 -> SpaceFreeZ143 (List.app cur [ch]).
Proof.
  unfold SpaceFreeZ143. intros cur ch Hfree Hch Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [auto|].
  simpl in Hin. destruct Hin as [->|[]]. auto.
Qed.

Lemma sentence_prefix_char_143 : forall input i cur words ch,
  0 <= i < Zlength input ->
  valid_string input ->
  SentencePrefix143 input i cur words ->
  ch = Znth i (c_string input) 0 ->
  ch <> 32 ->
  SentencePrefix143 input (i + 1) (List.app cur [ch]) words.
Proof.
  intros input i cur words ch Hi Hvalid Hprefix Hch Hnotspace.
  assert (Hnz : Znth i (c_string input) 0 <> 0).
  { destruct Hvalid as [_ Hvalid]. rewrite c_string_Znth_inside by exact Hi.
    apply Hvalid. exact Hi. }
  unfold SentencePrefix143 in *. destruct Hprefix as [[Hpre Hall]|[Hend _]]; [|lia].
  left. split.
  - pose proof (strncpy_sublist_succ input i Hnz ltac:(lia)
                  ltac:(unfold string_length; lia)) as Hsucc.
    rewrite <- Hsucc.
    rewrite Hpre, join_words_extend_last_143, Hch. reflexivity.
  - apply Forall_app in Hall. destruct Hall as [Hwords Hlast].
    apply Forall_app. split; [exact Hwords|].
    constructor.
    + apply space_free_extend_143; [inversion Hlast; assumption|exact Hnotspace].
    + constructor.
Qed.

Lemma current_word_start_char_143 : forall input i cur ch,
  0 <= i < Zlength input ->
  current_word_143 input i (-1) cur ->
  ch = Znth i (c_string input) 0 ->
  ch <> 32 ->
  current_word_143 input (i + 1) i [ch].
Proof.
  intros input i cur ch Hi Hcur Hch Hnotspace.
  unfold current_word_143 in *. destruct Hcur as [[_ Hcur]|Hbad]; [|lia].
  right. repeat split; try lia.
  - rewrite (sublist_single 0) by lia.
    rewrite c_string_Znth_inside in Hch by exact Hi.
    rewrite <- Hch. reflexivity.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - unfold SpaceFreeZ143. simpl. intros [Heq|[]]. auto.
Qed.

Lemma current_word_extend_char_143 : forall input i start cur ch,
  0 <= i < Zlength input ->
  valid_string input ->
  0 <= start ->
  current_word_143 input i start cur ->
  ch = Znth i (c_string input) 0 ->
  ch <> 32 ->
  current_word_143 input (i + 1) start (List.app cur [ch]).
Proof.
  intros input i start cur ch Hi Hvalid Hstart Hcur Hch Hnotspace.
  assert (Hnz : Znth i (c_string input) 0 <> 0).
  { destruct Hvalid as [_ Hvalid]. rewrite c_string_Znth_inside by exact Hi.
    apply Hvalid. exact Hi. }
  pose proof (current_word_active_143 _ _ _ _ Hcur Hstart) as
      [Hbounds [Hcurdef [Hcurlen Hfree]]].
  right. repeat split; try lia.
  - rewrite (sublist_split start (i + 1) i input) by lia.
    rewrite (sublist_single 0) by lia.
    rewrite c_string_Znth_inside in Hch by exact Hi.
    rewrite <- Hcurdef, <- Hch. reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - apply space_free_extend_143; assumption.
Qed.

Lemma sentence_prefix_finish_space_143 : forall input i cur words,
  0 <= i < Zlength input ->
  valid_string input ->
  SentencePrefix143 input i cur words ->
  Znth i (c_string input) 0 = 32 ->
  SentencePrefix143 input (i + 1) [] (List.app words [cur]).
Proof.
  intros input i cur words Hi Hvalid Hprefix Hspace.
  assert (Hnz : Znth i (c_string input) 0 <> 0) by lia.
  unfold SentencePrefix143 in *. destruct Hprefix as [[Hpre Hall]|[Hend _]]; [|lia].
  left. split.
  - pose proof (strncpy_sublist_succ input i Hnz ltac:(lia)
                  ltac:(unfold string_length; lia)) as Hsucc.
    rewrite <- Hsucc.
    rewrite Hpre, Hspace, join_words_finish_space_143. reflexivity.
  - apply Forall_app. split; [exact Hall|].
    constructor; [unfold SpaceFreeZ143; simpl; auto|constructor].
Qed.

Lemma sentence_prefix_finish_end_143 : forall input cur words start,
  0 <= start < Zlength input ->
  current_word_143 input (Zlength input) start cur ->
  SentencePrefix143 input (Zlength input) cur words ->
  SentencePrefix143 input (Zlength input) [] (List.app words [cur]).
Proof.
  intros input cur words start Hstart Hcur Hprefix.
  pose proof (current_word_active_143 _ _ _ _ Hcur ltac:(lia)) as
      [_ [_ [Hlen _]]].
  unfold SentencePrefix143 in *. destruct Hprefix as [[Hpre Hall]|[_ [Hnil _]]].
  - right. repeat split; try reflexivity; assumption.
  - subst cur. rewrite Zlength_nil in Hlen. lia.
Qed.

Lemma current_word_finished_143 : forall input i,
  current_word_143 input i (-1) [].
Proof. intros. unfold current_word_143. left. auto. Qed.

Lemma selected_join_nonempty_143 : forall words selected,
  PrimeLengthWordsZ143 words selected ->
  selected <> [] ->
  join_words_z_143 selected <> [].
Proof.
  intros words selected Hrel. induction Hrel; intros Hsel Hjoin; [contradiction| |].
  - destruct word as [|x word].
    + simpl in H. unfold IsPrime in H. destruct H as [Htwo _].
      simpl in Htwo. lia.
    + destruct selected; simpl in Hjoin; discriminate.
  - apply IHHrel; auto.
Qed.

Lemma copied_prime_output_143 : forall words selected word old prefix,
  PrimeLengthWordsZ143 words selected ->
  IsPrime (Z.to_nat (Zlength word)) ->
  old = join_words_z_143 selected ->
  copy_prefix_143 old prefix ->
  List.app prefix word = join_words_z_143 (List.app selected [word]).
Proof.
  intros words selected word old prefix Hrel Hprime Hold Hcopy.
  rewrite join_words_snoc_143. destruct selected as [|s selected].
  - simpl in *. destruct Hcopy as [[_ ->]|[Hbad _]]; [reflexivity|contradiction].
  - destruct Hcopy as [[Holdnil _]|[_ Hprefix]].
    + exfalso. apply (selected_join_nonempty_143 _ _ Hrel ltac:(discriminate)).
      rewrite <- Hold. exact Holdnil.
    + subst prefix. rewrite Hold. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma string_of_list_ascii_app_143 : forall a b,
  string_of_list_ascii (List.app a b) =
  String.append (string_of_list_ascii a) (string_of_list_ascii b).
Proof. induction a; intros b; simpl; [reflexivity|rewrite IHa; reflexivity]. Qed.

Lemma string_of_list_z_app_143 : forall a b,
  string_of_list_z_143 (List.app a b) =
  String.append (string_of_list_z_143 a) (string_of_list_z_143 b).
Proof.
  intros. unfold string_of_list_z_143. rewrite map_app.
  apply string_of_list_ascii_app_143.
Qed.

Lemma string_of_join_words_143 : forall words,
  string_of_list_z_143 (join_words_z_143 words) =
  String.concat " " (map string_of_list_z_143 words).
Proof.
  induction words as [|word words IH]; [reflexivity|].
  destruct words as [|word' words].
  - reflexivity.
  - change (string_of_list_z_143
              (List.app word (32 :: join_words_z_143 (word' :: words))) =
            String.append (string_of_list_z_143 word)
              (String.append " "
                (String.concat " "
                  (map string_of_list_z_143 (word' :: words))))).
    rewrite string_of_list_z_app_143.
    change (String.append (string_of_list_z_143 word)
              (String (ascii_of_z_143 32)
                (string_of_list_z_143 (join_words_z_143 (word' :: words)))) =
            String.append (string_of_list_z_143 word)
              (String.append " "
                (String.concat " "
                  (map string_of_list_z_143 (word' :: words))))).
    rewrite IH. reflexivity.
Qed.

Lemma string_of_list_z_length_143 : forall word,
  String.length (string_of_list_z_143 word) = List.length word.
Proof. induction word; simpl; auto. Qed.

Lemma ascii_of_z_space_143 : forall z,
  0 <= z <= 127 -> ascii_of_z_143 z = " "%char -> z = 32.
Proof.
  intros z Hz Heq. apply (f_equal nat_of_ascii) in Heq.
  unfold ascii_of_z_143 in Heq.
  rewrite nat_ascii_embedding in Heq by lia.
  change (Z.to_nat z = 32%nat) in Heq.
  apply (f_equal Z.of_nat) in Heq. rewrite Z2Nat.id in Heq by lia. lia.
Qed.

Lemma space_free_string_143 : forall word,
  ascii_range_z_143 word ->
  SpaceFreeZ143 word ->
  SpaceFree (string_of_list_z_143 word).
Proof.
  intros word Hrange Hfree.
  unfold SpaceFree, SpaceFreeZ143, string_of_list_z_143 in *.
  rewrite list_ascii_of_string_of_list_ascii.
  intro Hin. apply in_map_iff in Hin.
  destruct Hin as [z [Hzspace Hzin]].
  apply Hfree. assert (z = 32).
  - apply (ascii_of_z_space_143 z).
    + unfold ascii_range_z_143 in Hrange.
      rewrite Forall_forall in Hrange. apply Hrange; exact Hzin.
    + exact Hzspace.
  - subst z. exact Hzin.
Qed.

Lemma join_words_member_143 : forall words word z,
  In word words -> In z word -> In z (join_words_z_143 words).
Proof.
  induction words as [|a words IH]; intros word z Hin Hz; [contradiction|].
  destruct words as [|b words].
  - simpl in Hin. destruct Hin as [->|[]]. exact Hz.
  - simpl in Hin |- *. destruct Hin as [->|Hin].
    + apply in_or_app. left. exact Hz.
    + apply in_or_app. right. simpl. right.
      apply (IH word z Hin Hz).
Qed.

Lemma prime_words_to_strings_143 : forall words selected,
  PrimeLengthWordsZ143 words selected ->
  PrimeLengthWords (map string_of_list_z_143 words)
                   (map string_of_list_z_143 selected).
Proof.
  intros words selected Hrel. induction Hrel; simpl; constructor; auto.
  - rewrite string_of_list_z_length_143. rewrite Zlength_correct, Nat2Z.id in H.
    exact H.
  - rewrite string_of_list_z_length_143. rewrite Zlength_correct, Nat2Z.id in H.
    exact H.
Qed.

Lemma final_words_143 : forall input words selected,
  SentencePrefix143 input (Zlength input) [] words ->
  PrimeLengthWordsZ143 words selected ->
  exists final_words,
    input = join_words_z_143 final_words /\
    Forall SpaceFreeZ143 final_words /\
    PrimeLengthWordsZ143 final_words selected.
Proof.
  intros input words selected Hprefix Hprime.
  unfold SentencePrefix143 in Hprefix.
  assert (Hwhole : sublist 0 (Zlength input) input = input).
  { replace input with (List.app input (@nil Z)) at 2 by apply app_nil_r.
    apply sublist_app_exact1. }
  destruct Hprefix as [[Hjoin Hfree]|[_ [_ [Hjoin Hfree]]]].
  - exists (List.app words [(@nil Z)]). repeat split.
    + rewrite <- Hjoin, Hwhole. reflexivity.
    + exact Hfree.
    + apply prime_words_drop_snoc_143; [exact Hprime|].
      unfold IsPrime. intros [Htwo _]. simpl in Htwo. lia.
  - exists words. repeat split; auto. rewrite <- Hjoin, Hwhole. reflexivity.
Qed.

Lemma final_spec_z_143 : forall input words selected output,
  ascii_range_z_143 input ->
  SentencePrefix143 input (Zlength input) [] words ->
  PrimeLengthWordsZ143 words selected ->
  output = join_words_z_143 selected ->
  problem_143_spec_z input output.
Proof.
  intros input words selected output Hrange Hprefix Hprime Houtput.
  destruct (final_words_143 input words selected Hprefix Hprime) as
      [final_words [Hinput [Hfree Hfinalprime]]].
  unfold problem_143_spec_z, problem_143_spec.
  exists (map string_of_list_z_143 final_words).
  exists (map string_of_list_z_143 selected). split.
  - unfold SentenceWords. split.
    + rewrite <- string_of_join_words_143, <- Hinput. reflexivity.
    + rewrite Forall_forall. intros s Hs.
      apply in_map_iff in Hs. destruct Hs as [word [<- Hword]].
      apply space_free_string_143.
      * unfold ascii_range_z_143 in *. rewrite Forall_forall in Hrange.
        rewrite Forall_forall. intros z Hz.
        apply Hrange. rewrite Hinput.
        eapply join_words_member_143; eauto.
      * rewrite Forall_forall in Hfree. apply Hfree. exact Hword.
  - split.
    + apply prime_words_to_strings_143. exact Hfinalprime.
    + rewrite <- string_of_join_words_143, <- Houtput. reflexivity.
Qed.
