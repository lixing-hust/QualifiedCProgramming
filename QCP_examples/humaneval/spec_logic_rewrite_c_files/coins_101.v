Load "../spec/101".
Load "../StringClaude/string_bridge".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition problem_101_pre_z (input : list Z) : Prop :=
  problem_101_pre (string_of_list_z input).

Definition problem_101_spec_z
    (input : list Z) (output_words : list (list Z)) : Prop :=
  problem_101_spec
    (string_of_list_z input)
    (map string_of_list_z output_words).

Definition is_delimiter_z_101 (c : Z) : bool :=
  Z.eqb c 32 || Z.eqb c 44.

Definition delimiter_block_z_101 (block : list Z) : Prop :=
  Forall (fun c => is_delimiter_z_101 c = true) block.

Definition word_block_z_101 (word : list Z) : Prop :=
  word <> [] /\
  Forall (fun c => 0 <= c <= 255 /\ is_delimiter_z_101 c = false) word.

Fixpoint render_pairs_z_101
    (words gaps : list (list Z)) : list Z :=
  match words, gaps with
  | word :: words', gap :: gaps' =>
      List.app word (List.app gap (render_pairs_z_101 words' gaps'))
  | _, _ => []
  end.

Definition closed_words_z_101
    (prefix : list Z) (words : list (list Z)) : Prop :=
  (words = [] /\ delimiter_block_z_101 prefix) \/
  exists leading prior_words gaps last_word trailing,
    words = List.app prior_words [last_word] /\
    delimiter_block_z_101 leading /\
    List.length gaps = List.length prior_words /\
    Forall delimiter_block_z_101 gaps /\
    Forall (fun block => block <> []) gaps /\
    Forall word_block_z_101 prior_words /\
    word_block_z_101 last_word /\
    delimiter_block_z_101 trailing /\
    prefix =
      List.app leading
        (List.app (render_pairs_z_101 prior_words gaps)
          (List.app last_word trailing)).

Definition active_closed_words_z_101
    (prefix : list Z) (words : list (list Z)) : Prop :=
  (words = [] /\ delimiter_block_z_101 prefix) \/
  exists leading prior_words gaps last_word trailing,
    words = List.app prior_words [last_word] /\
    delimiter_block_z_101 leading /\
    List.length gaps = List.length prior_words /\
    Forall delimiter_block_z_101 gaps /\
    Forall (fun block => block <> []) gaps /\
    Forall word_block_z_101 prior_words /\
    word_block_z_101 last_word /\
    delimiter_block_z_101 trailing /\
    trailing <> [] /\
    prefix =
      List.app leading
        (List.app (render_pairs_z_101 prior_words gaps)
          (List.app last_word trailing)).

Definition open_words_z_101
    (prefix : list Z) (words : list (list Z)) (current : list Z) : Prop :=
  exists leading trailing_blocks,
    delimiter_block_z_101 leading /\
    List.length trailing_blocks = List.length words /\
    Forall delimiter_block_z_101 trailing_blocks /\
    Forall (fun block => block <> []) trailing_blocks /\
    Forall word_block_z_101 words /\
    word_block_z_101 current /\
    prefix =
      List.app leading
        (List.app
          (render_pairs_z_101 words trailing_blocks)
          current).

Definition split_prefix_state_101
    (input : list Z) (i start : Z) (words : list (list Z)) : Prop :=
  0 <= i <= Zlength input + 1 /\
  ((start = -1 /\
    ((i <= Zlength input /\
      active_closed_words_z_101
        (sublist 0 (Z.min i (Zlength input)) input) words) \/
     (i = Zlength input + 1 /\
      closed_words_z_101 input words))) \/
   (i <= Zlength input /\
    0 <= start < Z.min i (Zlength input) /\
    open_words_z_101
      (sublist 0 (Z.min i (Zlength input)) input)
      words
      (sublist start (Z.min i (Zlength input)) input))).

Fixpoint words_rows_heap_101
    (ptrs : list Z) (words : list (list Z)) : Assertion :=
  match ptrs, words with
  | p :: ps, word :: rest =>
      CharArray.full p (Zlength (c_string word)) (c_string word) **
      words_rows_heap_101 ps rest
  | [], [] => emp
  | _, _ => emp
  end.

Definition closing_delimiter_101 (input : list Z) (i n : Z) : Prop :=
  i = n \/
  (i < n /\
   (Znth i (string_lib.c_string input) 0 = 32 \/
    Znth i (string_lib.c_string input) 0 = 44)).

Definition ptr_array_contents_101
    (p used cap : Z) (ptrs : list Z) : Assertion :=
  PtrArray.seg p 0 used ptrs ** PtrArray.undef_seg p used cap.

Lemma words_rows_heap_101_nil :
  emp |-- words_rows_heap_101 [] [].
Proof. simpl. entailer!. Qed.

Lemma words_rows_heap_101_app : forall ptrs words p word,
  Zlength ptrs = Zlength words ->
  words_rows_heap_101 ptrs words **
  CharArray.full p (Zlength (c_string word)) (c_string word)
  |-- words_rows_heap_101 (ptrs ++ [p]) (words ++ [word]).
Proof.
  intros ptrs. induction ptrs as [|q ptrs IH]; intros words p word Hlen;
    destruct words as [|w words]; simpl in *.
  - rewrite derivable1_sepcon_comm. entailer!.
  - rewrite Zlength_cons in Hlen. rewrite Zlength_nil in Hlen.
    pose proof (Zlength_nonneg words). lia.
  - rewrite Zlength_cons in Hlen. rewrite Zlength_nil in Hlen.
    pose proof (Zlength_nonneg ptrs). lia.
  - rewrite Zlength_cons in Hlen. rewrite Zlength_cons in Hlen.
    assert (Htail : Zlength ptrs = Zlength words) by lia.
    sep_apply (IH words p word Htail). cancel.
Qed.

Lemma sublist_snoc_Znth_101 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.

Lemma delimiter_block_z_nil_101 : delimiter_block_z_101 [].
Proof. constructor. Qed.

Lemma delimiter_block_z_app_char_101 : forall block c,
  delimiter_block_z_101 block ->
  is_delimiter_z_101 c = true ->
  delimiter_block_z_101 (block ++ [c]).
Proof.
  intros block c Hb Hc. unfold delimiter_block_z_101 in *.
  rewrite Forall_forall in *. intros x Hx.
  apply in_app_or in Hx. destruct Hx as [Hx | Hx].
  - apply Hb. exact Hx.
  - simpl in Hx. destruct Hx as [-> | []]. exact Hc.
Qed.

Lemma word_block_z_single_101 : forall c,
  0 <= c <= 255 ->
  is_delimiter_z_101 c = false ->
  word_block_z_101 [c].
Proof.
  intros c Hrange Hdelim. split; [discriminate|].
  constructor; [auto|constructor].
Qed.

Lemma word_block_z_app_char_101 : forall word c,
  word_block_z_101 word ->
  0 <= c <= 255 ->
  is_delimiter_z_101 c = false ->
  word_block_z_101 (word ++ [c]).
Proof.
  intros word c [Hne Hall] Hrange Hdelim. split.
  - intro Hnil. apply app_eq_nil in Hnil. tauto.
  - rewrite Forall_forall in *. intros x Hx.
    apply in_app_or in Hx. destruct Hx as [Hx | Hx].
    + apply Hall. exact Hx.
    + simpl in Hx. destruct Hx as [-> | []]. auto.
Qed.

Lemma render_pairs_z_app_single_101 : forall words gaps word gap,
  List.length gaps = List.length words ->
  render_pairs_z_101 (words ++ [word]) (gaps ++ [gap]) =
  render_pairs_z_101 words gaps ++ word ++ gap.
Proof.
  induction words as [|w words IH]; intros gaps word gap Hlen.
  - destruct gaps.
    + cbn [render_pairs_z_101 List.app]. rewrite List.app_nil_r. reflexivity.
    + discriminate.
  - destruct gaps as [|g gaps]; [discriminate|].
    simpl in Hlen. inversion Hlen as [Htail].
    simpl. rewrite IH by exact Htail. rewrite !List.app_assoc. reflexivity.
Qed.

Lemma active_closed_to_closed_101 : forall prefix words,
  active_closed_words_z_101 prefix words ->
  closed_words_z_101 prefix words.
Proof.
  intros prefix words [Hempty | Hnonempty].
  - left. exact Hempty.
  - right. destruct Hnonempty as
      [leading [prior [gaps [last [trailing
       [Hwords [Hlead [Hlen [Hgaps [Hnonempty
       [Hprior [Hlast [Htrail [_ Hprefix]]]]]]]]]]]]]].
    exists leading, prior, gaps, last, trailing.
    tauto.
Qed.

Lemma active_closed_append_delimiter_101 : forall prefix words c,
  active_closed_words_z_101 prefix words ->
  is_delimiter_z_101 c = true ->
  active_closed_words_z_101 (prefix ++ [c]) words.
Proof.
  intros prefix words c Hclosed Hc.
  destruct Hclosed as [Hempty | Hnonempty].
  - destruct Hempty as [Hwords Hprefix].
    left. split; auto. apply delimiter_block_z_app_char_101; auto.
  - right. destruct Hnonempty as
      [leading [prior [gaps [last [trailing
       [Hwords [Hlead [Hlen [Hgaps [Hnonempty
       [Hprior [Hlast [Htrail [Htrail_ne Hprefix]]]]]]]]]]]]]].
    exists leading, prior, gaps, last, (trailing ++ [c]).
    repeat (first [assumption | split]).
    + apply delimiter_block_z_app_char_101; auto.
    + intro Hnil. apply app_eq_nil in Hnil. tauto.
    + rewrite Hprefix. rewrite !List.app_assoc. reflexivity.
Qed.

Lemma active_closed_start_word_101 : forall prefix words c,
  active_closed_words_z_101 prefix words ->
  0 <= c <= 255 ->
  is_delimiter_z_101 c = false ->
  open_words_z_101 (prefix ++ [c]) words [c].
Proof.
  intros prefix words c Hclosed Hrange Hc.
  destruct Hclosed as [Hempty | Hnonempty].
  - destruct Hempty as [Hwords Hprefix].
    subst words. exists prefix, [].
    repeat split; simpl; auto using word_block_z_single_101.
    discriminate.
  - destruct Hnonempty as
      [leading [prior [gaps [last [trailing
       [Hwords [Hlead [Hlen [Hgaps [Hnonempty
       [Hprior [Hlast [Htrail [Htrail_ne Hprefix]]]]]]]]]]]]]].
    exists leading, (gaps ++ [trailing]).
    repeat split.
    + exact Hlead.
    + rewrite app_length. simpl. rewrite Hlen, Hwords, app_length. simpl. lia.
    + apply Forall_app. split; auto.
    + apply Forall_app. split; auto.
    + rewrite Hwords. apply Forall_app. split; auto.
    + apply word_block_z_single_101; auto.
    + constructor; auto.
    + rewrite Hwords. rewrite render_pairs_z_app_single_101 by exact Hlen.
      rewrite Hprefix. rewrite !List.app_assoc. reflexivity.
Qed.

Lemma open_append_char_101 : forall prefix words current c,
  open_words_z_101 prefix words current ->
  0 <= c <= 255 ->
  is_delimiter_z_101 c = false ->
  open_words_z_101 (prefix ++ [c]) words (current ++ [c]).
Proof.
  intros prefix words current c Hopen Hrange Hc.
  destruct Hopen as
    [leading [gaps [Hlead [Hlen [Hgaps [Hnonempty
     [Hwords [Hcurrent Hprefix]]]]]]]].
  exists leading, gaps. repeat split; try assumption.
  - apply word_block_z_app_char_101; auto.
  - apply Forall_app. split.
    + exact (proj2 Hcurrent).
    + constructor; auto.
  - rewrite Hprefix. rewrite !List.app_assoc. reflexivity.
Qed.

Lemma open_close_delimiter_101 : forall prefix words current c,
  open_words_z_101 prefix words current ->
  is_delimiter_z_101 c = true ->
  active_closed_words_z_101 (prefix ++ [c]) (words ++ [current]).
Proof.
  intros prefix words current c Hopen Hc.
  destruct Hopen as
    [leading [gaps [Hlead [Hlen [Hgaps [Hnonempty
     [Hwords [Hcurrent Hprefix]]]]]]]].
  right. exists leading, words, gaps, current, [c].
  repeat split; try assumption; simpl; auto.
  - exact (proj1 Hcurrent).
  - exact (proj2 Hcurrent).
  - unfold delimiter_block_z_101. constructor; auto.
  - discriminate.
  - rewrite Hprefix. rewrite !List.app_assoc. reflexivity.
Qed.

Lemma open_finish_101 : forall prefix words current,
  open_words_z_101 prefix words current ->
  closed_words_z_101 prefix (words ++ [current]).
Proof.
  intros prefix words current Hopen.
  destruct Hopen as
    [leading [gaps [Hlead [Hlen [Hgaps [Hnonempty
     [Hwords [Hcurrent Hprefix]]]]]]]].
  right. exists leading, words, gaps, current, [].
  repeat split; try assumption; simpl; auto.
  - exact (proj1 Hcurrent).
  - exact (proj2 Hcurrent).
  - apply delimiter_block_z_nil_101.
  - rewrite List.app_nil_r. exact Hprefix.
Qed.

Lemma valid_string_Znth_range_101 : forall input i,
  string_lib.valid_string input ->
  0 <= i < Zlength input ->
  0 < Znth i input 0 < 256.
Proof.
  intros input i [Hall Hnonnull] Hi.
  specialize (Hall i Hi). specialize (Hnonnull i Hi). lia.
Qed.

Lemma is_delimiter_z_32_101 : is_delimiter_z_101 32 = true.
Proof. reflexivity. Qed.

Lemma is_delimiter_z_44_101 : is_delimiter_z_101 44 = true.
Proof. reflexivity. Qed.

Lemma is_delimiter_z_false_101 : forall c,
  c <> 32 -> c <> 44 -> is_delimiter_z_101 c = false.
Proof.
  intros c H32 H44. unfold is_delimiter_z_101.
  apply Bool.orb_false_iff. split; apply Z.eqb_neq; auto.
Qed.

Lemma Znth_c_string_input_101 : forall input i,
  0 <= i < Zlength input ->
  Znth i (string_lib.c_string input) 0 = Znth i input 0.
Proof.
  intros input i Hi. unfold string_lib.c_string.
  rewrite app_Znth1 by lia. reflexivity.
Qed.

Lemma split_prefix_state_init_101 : forall input,
  split_prefix_state_101 input 0 (-1) [].
Proof.
  intros input. unfold split_prefix_state_101.
  split; [pose proof (Zlength_nonneg input); lia|].
  left. split; [reflexivity|]. left. split.
  - pose proof (Zlength_nonneg input). lia.
  - left. split; [reflexivity|].
    replace (Z.min 0 (Zlength input)) with 0 by
      (pose proof (Zlength_nonneg input); lia).
    change (delimiter_block_z_101 []). apply delimiter_block_z_nil_101.
Qed.

Lemma split_prefix_state_active_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  start < 0 ->
  i <= Zlength input ->
  start = -1 /\ active_closed_words_z_101 (sublist 0 i input) words.
Proof.
  intros input i start words [_ Hstate] Hstart Hi.
  destruct Hstate as [[Hminus [Hactive | Hfinal]] | [_ [Hnonneg _]]].
  - split; [exact Hminus|]. destruct Hactive as [_ Hactive].
    replace (Z.min i (Zlength input)) with i in Hactive by lia.
    exact Hactive.
  - destruct Hfinal as [Hfinal _]. lia.
  - lia.
Qed.

Lemma split_prefix_state_open_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  0 <= start ->
  i <= Zlength input ->
  0 <= start < i /\
  open_words_z_101 (sublist 0 i input) words (sublist start i input).
Proof.
  intros input i start words [_ Hstate] Hstart Hi.
  destruct Hstate as [[Hminus _] | [_ [Hbounds Hopen]]].
  - lia.
  - replace (Z.min i (Zlength input)) with i in Hbounds, Hopen by lia.
    split; assumption.
Qed.

Lemma split_prefix_state_final_closed_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  i > Zlength input ->
  i <= Zlength input + 1 ->
  start = -1 /\ i = Zlength input + 1 /\ closed_words_z_101 input words.
Proof.
  intros input i start words [_ Hstate] Hgt Hle.
  destruct Hstate as [[Hminus [Hactive | Hfinal]] | [Hi [_ _]]].
  - destruct Hactive as [Hi _]. lia.
  - destruct Hfinal as [Hi Hclosed]. auto.
  - lia.
Qed.

Lemma split_prefix_state_closed_step_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  start < 0 ->
  0 <= i < Zlength input ->
  is_delimiter_z_101 (Znth i input 0) = true ->
  split_prefix_state_101 input (i + 1) start words.
Proof.
  intros input i start words Hstate Hstart Hi Hdelimiter.
  pose proof (split_prefix_state_active_101 _ _ _ _ Hstate Hstart (ltac:(lia)))
    as [Hminus Hactive].
  subst start. unfold split_prefix_state_101.
  split; [lia|]. left. split; [reflexivity|]. left. split; [lia|].
  replace (Z.min (i + 1) (Zlength input)) with (i + 1) by lia.
  rewrite sublist_snoc_Znth_101 by lia.
  apply active_closed_append_delimiter_101; assumption.
Qed.

Lemma split_prefix_state_start_step_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  start < 0 ->
  string_lib.valid_string input ->
  0 <= i < Zlength input ->
  is_delimiter_z_101 (Znth i input 0) = false ->
  split_prefix_state_101 input (i + 1) i words.
Proof.
  intros input i start words Hstate Hstart Hvalid Hi Hdelimiter.
  pose proof (split_prefix_state_active_101 _ _ _ _ Hstate Hstart (ltac:(lia)))
    as [_ Hactive].
  pose proof (valid_string_Znth_range_101 _ _ Hvalid Hi) as Hrange.
  unfold split_prefix_state_101. split; [lia|]. right. split; [lia|].
  replace (Z.min (i + 1) (Zlength input)) with (i + 1) by lia.
  split; [lia|].
  rewrite sublist_snoc_Znth_101 by lia.
  replace (sublist i (i + 1) input) with [Znth i input 0]
    by (symmetry; apply sublist_single; lia).
  apply active_closed_start_word_101; try assumption; lia.
Qed.

Lemma split_prefix_state_open_step_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  0 <= start ->
  string_lib.valid_string input ->
  0 <= i < Zlength input ->
  is_delimiter_z_101 (Znth i input 0) = false ->
  split_prefix_state_101 input (i + 1) start words.
Proof.
  intros input i start words Hstate Hstart Hvalid Hi Hdelimiter.
  pose proof (split_prefix_state_open_101 _ _ _ _ Hstate Hstart (ltac:(lia)))
    as [Hbounds Hopen].
  pose proof (valid_string_Znth_range_101 _ _ Hvalid Hi) as Hrange.
  unfold split_prefix_state_101. split; [lia|]. right. split; [lia|].
  replace (Z.min (i + 1) (Zlength input)) with (i + 1) by lia.
  split; [lia|].
  rewrite sublist_snoc_Znth_101 by lia.
  rewrite (sublist_split start (i + 1) i input) by lia.
  rewrite (sublist_single start i input) by lia.
  rewrite (Znth_indep input i start 0) by lia.
  apply open_append_char_101; try assumption; lia.
Qed.

Lemma split_prefix_state_close_step_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  0 <= start ->
  0 <= i < Zlength input ->
  is_delimiter_z_101 (Znth i input 0) = true ->
  split_prefix_state_101 input (i + 1) (-1)
    (words ++ [sublist start i input]).
Proof.
  intros input i start words Hstate Hstart Hi Hdelimiter.
  pose proof (split_prefix_state_open_101 _ _ _ _ Hstate Hstart (ltac:(lia)))
    as [_ Hopen].
  unfold split_prefix_state_101. split; [lia|]. left.
  split; [reflexivity|]. left. split; [lia|].
  replace (Z.min (i + 1) (Zlength input)) with (i + 1) by lia.
  rewrite sublist_snoc_Znth_101 by lia.
  apply open_close_delimiter_101; assumption.
Qed.

Lemma split_prefix_state_finish_closed_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  start < 0 ->
  i = Zlength input ->
  split_prefix_state_101 input (i + 1) start words.
Proof.
  intros input i start words Hstate Hstart Hi.
  pose proof (split_prefix_state_active_101 _ _ _ _ Hstate Hstart (ltac:(lia)))
    as [Hminus Hactive].
  subst start i. unfold split_prefix_state_101.
  split; [pose proof (Zlength_nonneg input); lia|].
  left. split; [reflexivity|]. right. split; [lia|].
  replace (sublist 0 (Zlength input) input) with input in Hactive
    by (symmetry; apply sublist_self; reflexivity).
  apply active_closed_to_closed_101. exact Hactive.
Qed.

Lemma split_prefix_state_finish_open_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  0 <= start ->
  i = Zlength input ->
  split_prefix_state_101 input (i + 1) (-1)
    (words ++ [sublist start i input]).
Proof.
  intros input i start words Hstate Hstart Hi.
  pose proof (split_prefix_state_open_101 _ _ _ _ Hstate Hstart (ltac:(lia)))
    as [_ Hopen].
  subst i. unfold split_prefix_state_101.
  split; [pose proof (Zlength_nonneg input); lia|].
  left. split; [reflexivity|]. right. split; [lia|].
  replace (sublist 0 (Zlength input) input) with input in Hopen.
  - apply open_finish_101. exact Hopen.
  - symmetry. apply sublist_self. reflexivity.
Qed.

Lemma split_prefix_state_close_with_closing_101 :
  forall input i start words n,
  split_prefix_state_101 input i start words ->
  0 <= start ->
  i <= n ->
  n = Zlength input ->
  closing_delimiter_101 input i n ->
  split_prefix_state_101 input (i + 1) (-1)
    (words ++ [sublist start i input]).
Proof.
  intros input i start words n Hstate Hstart Hi Hn Hclosing.
  assert (Hnonneg : 0 <= i) by (destruct Hstate as [Hbounds _]; lia).
  destruct Hclosing as [-> | [Hlt [Hspace | Hcomma]]].
  - apply split_prefix_state_finish_open_101; try assumption; lia.
  - apply split_prefix_state_close_step_101; try assumption; try lia.
    rewrite (Znth_c_string_input_101 input i) in Hspace by lia.
    rewrite Hspace. apply is_delimiter_z_32_101.
  - apply split_prefix_state_close_step_101; try assumption; try lia.
    rewrite (Znth_c_string_input_101 input i) in Hcomma by lia.
    rewrite Hcomma. apply is_delimiter_z_44_101.
Qed.

Lemma delimiter_z_maps_ascii_101 : forall c,
  is_delimiter_z_101 c = true ->
  is_delimiter (ascii_of_z c) = true.
Proof.
  intros c Hdelimiter. unfold is_delimiter_z_101 in Hdelimiter.
  apply Bool.orb_true_iff in Hdelimiter.
  destruct Hdelimiter as [Hc | Hc]; apply Z.eqb_eq in Hc; subst; reflexivity.
Qed.

Lemma nondelimiter_z_maps_ascii_101 : forall c,
  0 <= c < 256 ->
  is_delimiter_z_101 c = false ->
  is_delimiter (ascii_of_z c) = false.
Proof.
  intros c Hrange Hdelimiter.
  unfold is_delimiter_z_101 in Hdelimiter.
  apply Bool.orb_false_iff in Hdelimiter.
  destruct Hdelimiter as [Hspace Hcomma].
  apply Z.eqb_neq in Hspace. apply Z.eqb_neq in Hcomma.
  pose proof (nat_of_ascii_ascii_of_z c Hrange) as Hnat.
  assert (HnatZ : Z.of_nat (nat_of_ascii (ascii_of_z c)) = c).
  { rewrite Hnat, Z2Nat.id by lia. reflexivity. }
  destruct (ascii_of_z c) as [b0 b1 b2 b3 b4 b5 b6 b7] eqn:Hascii.
  repeat destruct b0; repeat destruct b1; repeat destruct b2;
    repeat destruct b3; repeat destruct b4; repeat destruct b5;
    repeat destruct b6; repeat destruct b7;
    simpl in HnatZ |- *; try reflexivity; lia.
Qed.

Lemma delimiter_block_z_maps_ascii_101 : forall block,
  delimiter_block_z_101 block ->
  delimiter_block (map ascii_of_z block).
Proof.
  intros block Hblock. induction Hblock as [|c block Hc Hblock IH]; simpl.
  - constructor.
  - constructor; auto using delimiter_z_maps_ascii_101.
Qed.

Lemma word_block_z_maps_ascii_101 : forall word,
  word_block_z_101 word ->
  word_block (map ascii_of_z word).
Proof.
  intros word [Hnonempty Hword]. split.
  - destruct word; [contradiction|discriminate].
  - clear Hnonempty. induction Hword as [|c word [Hrange Hdelimiter] Hword IH]; simpl.
    + constructor.
    + constructor.
      * apply nondelimiter_z_maps_ascii_101; try assumption; lia.
      * exact IH.
Qed.

Lemma Forall_map_delimiter_blocks_101 : forall blocks,
  Forall delimiter_block_z_101 blocks ->
  Forall delimiter_block (map (map ascii_of_z) blocks).
Proof.
  intros blocks Hblocks. induction Hblocks; simpl; constructor; auto.
  apply delimiter_block_z_maps_ascii_101. assumption.
Qed.

Lemma Forall_map_word_blocks_101 : forall words,
  Forall word_block_z_101 words ->
  Forall word_block (map (map ascii_of_z) words).
Proof.
  intros words Hwords. induction Hwords; simpl; constructor; auto.
  apply word_block_z_maps_ascii_101. assumption.
Qed.

Lemma map_blocks_preserves_nonempty_101 : forall blocks,
  Forall (fun block : list Z => block <> []) blocks ->
  Forall (fun block : list ascii => block <> [])
    (map (map ascii_of_z) blocks).
Proof.
  intros blocks Hblocks. induction Hblocks as [|block blocks Hblock Hblocks IH]; simpl.
  - constructor.
  - constructor; auto. destruct block; [contradiction|discriminate].
Qed.

Lemma render_pairs_z_maps_ascii_101 : forall words gaps,
  List.length gaps = List.length words ->
  map ascii_of_z (render_pairs_z_101 words gaps) =
  List.concat
    (map (fun pair => fst pair ++ snd pair)
      (combine (map (map ascii_of_z) words)
               (map (map ascii_of_z) gaps))).
Proof.
  induction words as [|word words IH]; intros gaps Hlen.
  - destruct gaps; [reflexivity|discriminate].
  - destruct gaps as [|gap gaps]; [discriminate|].
    simpl in Hlen. inversion Hlen as [Htail]. simpl.
    rewrite !map_app. rewrite IH by exact Htail.
    rewrite List.app_assoc. reflexivity.
Qed.

Lemma removelast_app_single_101 : forall {A : Type} (l : list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros A l. induction l as [|a l IH]; intros x; simpl.
  - reflexivity.
  - destruct l as [|b l].
    + constructor.
    + simpl in IH |- *. rewrite IH. reflexivity.
Qed.

Lemma closed_words_z_to_rel_101 : forall input words,
  closed_words_z_101 input words ->
  words_string_rel
    (map ascii_of_z input)
    (map (map ascii_of_z) words).
Proof.
  intros input words [Hempty | Hclosed].
  - destruct Hempty as [-> Hinput].
    exists (map ascii_of_z input), [].
    split.
    + apply delimiter_block_z_maps_ascii_101. exact Hinput.
    + split; [reflexivity|].
      split; [constructor|].
      split.
      * change (Forall (fun block : list ascii => block <> []) []). constructor.
      * split; [constructor|]. simpl. rewrite List.app_nil_r. reflexivity.
  - destruct Hclosed as
      (leading & prior & gaps & last & trailing & Hwords & Hleading & Hlen &
       Hgaps & Hnonempty & Hprior & Hlast & Htrailing & Hinput).
    subst words.
    exists (map ascii_of_z leading),
      (map (map ascii_of_z) (gaps ++ [trailing])).
    repeat split.
    + apply delimiter_block_z_maps_ascii_101. exact Hleading.
    + rewrite !map_length, !app_length. simpl. rewrite Hlen. lia.
    + rewrite map_app. simpl. apply Forall_app. split.
      * apply Forall_map_delimiter_blocks_101. exact Hgaps.
      * constructor; auto using delimiter_block_z_maps_ascii_101.
    + rewrite map_app. simpl. rewrite removelast_app_single_101.
      apply map_blocks_preserves_nonempty_101. exact Hnonempty.
    + rewrite map_app. simpl. apply Forall_app. split.
      * apply Forall_map_word_blocks_101. exact Hprior.
      * constructor; auto using word_block_z_maps_ascii_101.
    + rewrite Hinput.
      rewrite <- (render_pairs_z_maps_ascii_101
        (prior ++ [last]) (gaps ++ [trailing])).
      * rewrite render_pairs_z_app_single_101 by exact Hlen.
        rewrite !map_app. reflexivity.
      * rewrite !app_length. simpl. lia.
Qed.

Lemma string_of_list_z_map_ascii_101 : forall word,
  string_of_list_ascii (map ascii_of_z word) = string_of_list_z word.
Proof. induction word; simpl; congruence. Qed.

Lemma closed_words_z_problem_spec_101 : forall input words,
  closed_words_z_101 input words ->
  problem_101_spec_z input words.
Proof.
  intros input words Hclosed.
  unfold problem_101_spec_z, problem_101_spec.
  exists (map (map ascii_of_z) words). split.
  - rewrite list_ascii_of_string_string_of_list_z.
    apply closed_words_z_to_rel_101. exact Hclosed.
  - rewrite map_map. apply map_ext. intros word.
    symmetry. apply string_of_list_z_map_ascii_101.
Qed.

Lemma split_prefix_state_problem_spec_101 : forall input i start words,
  split_prefix_state_101 input i start words ->
  i > Zlength input ->
  i <= Zlength input + 1 ->
  problem_101_spec_z input words.
Proof.
  intros input i start words Hstate Hgt Hle.
  pose proof (split_prefix_state_final_closed_101 _ _ _ _ Hstate Hgt Hle)
    as [_ [_ Hclosed]].
  apply closed_words_z_problem_spec_101. exact Hclosed.
Qed.

Lemma allowed_ascii_z_range_101 : forall c,
  0 <= c < 256 ->
  (((65 <= nat_of_ascii (ascii_of_z c) /\ nat_of_ascii (ascii_of_z c) <= 90)%nat) \/
   ((97 <= nat_of_ascii (ascii_of_z c) /\ nat_of_ascii (ascii_of_z c) <= 122)%nat) \/
   ascii_of_z c = ","%char \/ ascii_of_z c = " "%char) ->
  0 <= c <= 127.
Proof.
  intros c Hrange Hallowed.
  pose proof (nat_of_ascii_ascii_of_z c Hrange) as Hnat.
  assert (Hback : Z.of_nat (Z.to_nat c) = c) by (apply Z2Nat.id; lia).
  destruct Hallowed as [Hupper | [Hlower | [Hcomma | Hspace]]].
  - rewrite Hnat in Hupper. lia.
  - rewrite Hnat in Hlower. lia.
  - apply (f_equal nat_of_ascii) in Hcomma. simpl in Hcomma.
    rewrite Hnat in Hcomma. apply (f_equal Z.of_nat) in Hcomma.
    simpl in Hcomma. rewrite Hback in Hcomma. lia.
  - apply (f_equal nat_of_ascii) in Hspace. simpl in Hspace.
    rewrite Hnat in Hspace. apply (f_equal Z.of_nat) in Hspace.
    simpl in Hspace. rewrite Hback in Hspace. lia.
Qed.

Lemma problem_pre_valid_all_ascii_101 : forall input,
  problem_101_pre_z input ->
  string_lib.valid_string input ->
  all_ascii input.
Proof.
  intros input _ [Hall _]. exact Hall.
Qed.

Lemma problem_pre_valid_sublist_ascii_101 : forall input lo hi,
  problem_101_pre_z input ->
  string_lib.valid_string input ->
  0 <= lo <= hi ->
  hi <= Zlength input ->
  all_ascii (sublist lo hi input).
Proof.
  intros input lo hi Hpre Hvalid Hbounds Hhi.
  pose proof (problem_pre_valid_all_ascii_101 input Hpre Hvalid) as Hall.
  intros k Hk. rewrite Zlength_sublist in Hk by lia.
  rewrite Znth_sublist by lia. apply Hall. lia.
Qed.

Lemma sublist_c_string_prefix_101 : forall input lo hi,
  0 <= lo <= hi ->
  hi <= Zlength input ->
  sublist lo hi (string_lib.c_string input) = sublist lo hi input.
Proof.
  intros input lo hi Hbounds Hhi. unfold string_lib.c_string.
  apply sublist_split_app_l; lia.
Qed.

Lemma split_c_string_contents_101 : forall input start i n,
  0 <= start <= i ->
  i <= n ->
  Zlength input = n ->
  (sublist 0 start (string_lib.c_string input) ++ sublist start i input) ++
    sublist i (n + 1) (string_lib.c_string input) =
  string_lib.c_string input.
Proof.
  intros input start i n Hstart Hi Hlen.
  assert (Hclen : Zlength (string_lib.c_string input) = n + 1).
  { unfold string_lib.c_string. rewrite Zlength_app, Zlength_cons,
      Zlength_nil, Hlen. lia. }
  rewrite <- (sublist_c_string_prefix_101 input start i Hstart (ltac:(lia))).
  rewrite <- (sublist_split 0 i start (string_lib.c_string input)) by lia.
  rewrite <- (sublist_split 0 (n + 1) i (string_lib.c_string input)) by lia.
  replace (n + 1) with (Zlength (string_lib.c_string input)) by lia.
  apply sublist_self. reflexivity.
Qed.

Lemma merge_c_string_101 : forall input s start i n input_pre input_post,
  0 <= start <= i -> i <= n -> Zlength input = n ->
  input_pre = sublist 0 start (string_lib.c_string input) ->
  input_post = sublist i (n + 1) (string_lib.c_string input) ->
  CharArray.seg s 0 start input_pre **
  CharArray.full (s + start * sizeof(CHAR)) (i - start)
    (sublist start i input) **
  CharArray.seg s i (n + 1) input_post |--
  string_lib.store_string s input.
Proof.
  intros input s start i n input_pre input_post Hstart Hi Hlen -> ->.
  unfold string_lib.store_string.
  sep_apply_l_atomic (CharArray.full_to_seg
    (s + start * sizeof(CHAR)) (i - start) (sublist start i input)).
  rewrite <- (CharArray.seg_0_shift s start i (sublist start i input)).
  sep_apply_l_atomic (CharArray.seg_merge_to_seg s 0 start i
    (sublist 0 start (string_lib.c_string input)) (sublist start i input) Hstart).
  sep_apply_l_atomic (CharArray.seg_merge_to_full s 0 i (n + 1)
    (sublist 0 start (string_lib.c_string input) ++ sublist start i input)
    (sublist i (n + 1) (string_lib.c_string input)) (ltac:(lia))).
  unfold string_lib.string_length. rewrite Hlen.
  rewrite split_c_string_contents_101 by lia.
  replace (s + 0 * sizeof(CHAR)) with s by lia.
  replace (n + 1 - 0) with (n + 1) by lia. entailer!.
Qed.

Lemma c_string_sublist_shape_101 : forall input start i len,
  len = i - start ->
  Zlength (sublist start i input) = len ->
  Zlength (string_lib.c_string (sublist start i input)) = len + 1.
Proof.
  intros input start i len _ Hlen.
  unfold string_lib.c_string. rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen. lia.
Qed.

Lemma prepare_word_copy_heap_101 : forall input s retval start i n,
  0 <= start < i ->
  i <= n ->
  n = string_lib.string_length input ->
  CharArray.undef_full retval ((i - start) + 1) **
  CharArray.full s (string_lib.string_length input + 1)
    (string_lib.c_string input) |--
  CharArray.seg s 0 start
    (sublist 0 start (string_lib.c_string input)) **
  CharArray.full (s + start * sizeof(CHAR)) (i - start)
    (sublist start i input) **
  CharArray.seg s i (n + 1)
    (sublist i (n + 1) (string_lib.c_string input)) **
  CharArray.undef_full retval (i - start) **
  CharArray.undef_seg retval (i - start) ((i - start) + 1).
Proof.
  intros input s retval start i n Hstart Hi Hlen.
  assert (HZ : Zlength input = n).
  { unfold string_lib.string_length in Hlen. lia. }
  rewrite <- Hlen.
  sep_apply_l_atomic (CharArray.full_split_to_seg s start (n + 1)
    (string_lib.c_string input)); [apply derivable1s_coq_prop_r; lia|].
  sep_apply_l_atomic (CharArray.seg_split_to_seg s start i (n + 1)
    (sublist start (n + 1) (string_lib.c_string input)));
    [apply derivable1s_coq_prop_r; lia|].
  sep_apply_l_atomic (CharArray.seg_to_full s start i
    (sublist 0 (i - start)
      (sublist start (n + 1) (string_lib.c_string input)))).
  sep_apply_l_atomic (CharArray.undef_full_split_to_undef_seg retval
    (i - start) ((i - start) + 1));
    [apply derivable1s_coq_prop_r; lia|].
  repeat rewrite Zsublist_Zsublist by lia.
  rewrite sublist_c_string_prefix_101 by lia.
  replace (0 + start) with start by lia.
  replace (i - start + start) with i by lia.
  replace (n + 1 - start + start) with (n + 1) by lia.
  sep_apply_l_atomic (CharArray.undef_seg_to_undef_full retval 0 (i - start)).
  replace (retval + 0 * sizeof(CHAR)) with retval by lia.
  replace (i - start - 0) with (i - start) by lia.
  entailer!.
Qed.
