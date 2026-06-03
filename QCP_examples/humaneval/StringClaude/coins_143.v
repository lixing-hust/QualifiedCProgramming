Load "../spec/143".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_143_pre_z (sentence : list Z) : Prop :=
  problem_143_pre (string_of_list_z sentence).

Definition problem_143_spec_z (sentence output : list Z) : Prop :=
  problem_143_spec (string_of_list_z sentence) (string_of_list_z output).

Definition ascii_range_z (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition z_of_ascii (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Fixpoint list_z_of_string (s : string) : list Z :=
  match s with
  | EmptyString => []
  | String c rest => z_of_ascii c :: list_z_of_string rest
  end.

Definition prime_len_flag_z (n : Z) : Z :=
  if is_prime_bool (Z.to_nat n) then 1 else 0.

Fixpoint split_words_z_aux (cur rest : list Z) : list (list Z) :=
  match rest with
  | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
  | h :: t =>
      if Z.eqb h 32 then
        match cur with
        | [] => split_words_z_aux [] t
        | _ => rev cur :: split_words_z_aux [] t
        end
      else split_words_z_aux (h :: cur) t
  end.

Definition split_words_z (sentence : list Z) : list (list Z) :=
  split_words_z_aux [] sentence.

Fixpoint split_words_ascii_aux (cur rest : list ascii) : list (list ascii) :=
  match rest with
  | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
  | h :: t =>
      if Ascii.eqb h " "%char then
        match cur with
        | [] => split_words_ascii_aux [] t
        | _ => rev cur :: split_words_ascii_aux [] t
        end
      else split_words_ascii_aux (h :: cur) t
  end.

Definition split_words_ascii (sentence : list ascii) : list (list ascii) :=
  split_words_ascii_aux [] sentence.

Definition split_words_spec_aux (cur rest : list ascii) : list (list ascii) :=
  (fix aux (cur rest : list ascii) {struct rest} : list (list ascii) :=
     match rest with
     | [] =>
         match cur with
         | [] => []
         | _ => [rev cur]
         end
     | h :: t =>
         if Ascii.eqb h " "%char then
           match cur with
           | [] => aux [] t
           | _ => rev cur :: aux [] t
           end
         else aux (h :: cur) t
     end) cur rest.

Definition words_output_ascii (s : list ascii) : list ascii :=
  join_words
    (List.filter (fun w => is_prime_bool (List.length w)) (split_words s)).

Fixpoint join_words_z (ws : list (list Z)) : list Z :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest => w ++ [32] ++ join_words_z rest
  end.

Definition selected_words_z (sentence : list Z) : list (list Z) :=
  List.filter (fun w => Z.eqb (prime_len_flag_z (Zlength w)) 1)
    (split_words_z sentence).

Definition words_in_sentence_output_z (sentence : list Z) : list Z :=
  join_words_z (selected_words_z sentence).

Definition words_in_sentence_prefix_z (i : Z) (sentence : list Z) : list Z :=
  words_in_sentence_output_z (sublist 0 i sentence).

Lemma split_words_spec_aux_eq : forall cur rest,
  split_words_spec_aux cur rest = split_words_ascii_aux cur rest.
Proof.
  unfold split_words_spec_aux.
  intros cur rest.
  revert cur.
  induction rest as [| h t IH]; intros cur; simpl.
  - destruct cur; reflexivity.
  - destruct (Ascii.eqb h " "%char); destruct cur; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma split_words_eq_spec_aux : forall s,
  split_words s = split_words_spec_aux [] s.
Proof.
  intros s.
  destruct s as [| h t].
  - reflexivity.
  - unfold split_words, split_words_spec_aux.
    simpl.
    destruct (Ascii.eqb h " "%char); reflexivity.
Qed.

Lemma split_words_spec_aux_app_space : forall cur rest,
  split_words_spec_aux cur (rest ++ [" "%char]) =
  split_words_spec_aux cur rest.
Proof.
  unfold split_words_spec_aux.
  intros cur rest.
  revert cur.
  induction rest as [| h t IH]; intros cur; simpl.
  - destruct cur; simpl; reflexivity.
  - destruct (Ascii.eqb h " "%char); destruct cur; simpl; rewrite ?IH; try reflexivity.
Qed.

Lemma split_words_app_space : forall s,
  split_words (s ++ [" "%char]) = split_words s.
Proof.
  intros s.
  rewrite !split_words_eq_spec_aux.
  apply split_words_spec_aux_app_space.
Qed.

Lemma words_output_ascii_app_space : forall s,
  words_output_ascii (s ++ [" "%char]) = words_output_ascii s.
Proof.
  intros s.
  unfold words_output_ascii.
  rewrite split_words_app_space.
  reflexivity.
Qed.

Lemma list_z_of_string_string_of_list_ascii : forall s,
  list_z_of_string (string_of_list_ascii s) = map z_of_ascii s.
Proof.
  induction s as [| c rest IH]; simpl; congruence.
Qed.

Lemma ascii_of_z_32 : ascii_of_z 32 = " "%char.
Proof.
  reflexivity.
Qed.

Lemma list_ascii_of_string_string_of_list_z_app_space : forall sentence,
  list_ascii_of_string (string_of_list_z (sentence ++ [32])) =
  list_ascii_of_string (string_of_list_z sentence) ++ [" "%char].
Proof.
  intros sentence.
  rewrite !list_ascii_of_string_string_of_list_z.
  rewrite map_app.
  simpl.
  rewrite ascii_of_z_32.
  reflexivity.
Qed.

Lemma split_words_z_aux_app_space : forall cur rest,
  split_words_z_aux cur (rest ++ [32]) =
  split_words_z_aux cur rest.
Proof.
  intros cur rest.
  revert cur.
  induction rest as [| h t IH]; intros cur; simpl.
  - destruct cur; simpl; reflexivity.
  - destruct (Z.eqb h 32); destruct cur; simpl; rewrite ?IH; try reflexivity.
Qed.

Lemma split_words_z_app_space : forall sentence,
  split_words_z (sentence ++ [32]) = split_words_z sentence.
Proof.
  intros sentence.
  unfold split_words_z.
  apply split_words_z_aux_app_space.
Qed.

Lemma words_in_sentence_output_z_app_space : forall sentence,
  words_in_sentence_output_z (sentence ++ [32]) =
  words_in_sentence_output_z sentence.
Proof.
  intros sentence.
  unfold words_in_sentence_output_z, selected_words_z.
  rewrite split_words_z_app_space.
  reflexivity.
Qed.

Lemma words_in_sentence_prefix_z_skip_space : forall sentence i,
  0 <= i < Zlength sentence ->
  Znth i (sentence ++ [0]) 0 = 32 ->
  words_in_sentence_prefix_z (i + 1) sentence =
  words_in_sentence_prefix_z i sentence.
Proof.
  intros sentence i Hi Hspace.
  unfold words_in_sentence_prefix_z.
  assert (sublist 0 (i + 1) sentence = sublist 0 i sentence ++ [32]) as Hsub.
  {
    rewrite (sublist_split 0 (i + 1) i sentence);
      [| lia | rewrite <- Zlength_correct; lia].
    rewrite (sublist_single i sentence 0) by (rewrite <- Zlength_correct; lia).
    rewrite app_Znth1 in Hspace by lia.
    rewrite Hspace.
    reflexivity.
  }
  rewrite Hsub.
  apply words_in_sentence_output_z_app_space.
Qed.

Definition prime_loop_state_z (n j composite : Z) : Prop :=
  composite = 1 <->
    exists d, 2 <= d < j /\ Z.rem n d = 0.

Definition append_selected_word_z
    (out prefix : list Z) (start len : Z) : list Z :=
  if Z.eqb (prime_len_flag_z len) 1 then
    out ++ (if Z.eqb (Zlength out) 0 then [] else [32]) ++
    sublist start (start + len) prefix
  else out.

Definition word_chars_z (sentence : list Z) (start i : Z) : Prop :=
  forall p, start <= p < i -> Znth p (sentence ++ [0]) 0 <> 32.

Definition word_start_z (sentence : list Z) (start : Z) : Prop :=
  start = 0 \/ Znth (start - 1) (sentence ++ [0]) 0 = 32.

Definition scan_ready_z (sentence : list Z) (len i : Z) : Prop :=
  i = 0 \/
  i = len \/
  Znth i (sentence ++ [0]) 0 = 32 \/
  Znth (i - 1) (sentence ++ [0]) 0 = 32.

Definition word_copy_prefix_z (start k : Z) (sentence : list Z) : list Z :=
  words_in_sentence_prefix_z start sentence ++
  (if Z.eqb (Zlength (words_in_sentence_prefix_z start sentence)) 0
   then [] else [32]) ++
  sublist start (start + k) sentence.

Lemma word_chars_z_empty : forall sentence start,
  word_chars_z sentence start start.
Proof.
  unfold word_chars_z.
  intros sentence start p Hp.
  lia.
Qed.

Lemma word_chars_z_step : forall sentence start i,
  word_chars_z sentence start i ->
  Znth i (sentence ++ [0]) 0 <> 32 ->
  word_chars_z sentence start (i + 1).
Proof.
  unfold word_chars_z.
  intros sentence start i Hchars Hi p Hp.
  assert (p < i \/ p = i) as [Hlt | ->] by lia.
  - apply Hchars. lia.
  - exact Hi.
Qed.

Lemma scan_ready_z_0 : forall sentence len,
  scan_ready_z sentence len 0.
Proof.
  unfold scan_ready_z.
  auto.
Qed.

Lemma scan_ready_z_at_end : forall sentence len i,
  i = len ->
  scan_ready_z sentence len i.
Proof.
  unfold scan_ready_z.
  auto.
Qed.

Lemma scan_ready_z_at_space : forall sentence len i,
  Znth i (sentence ++ [0]) 0 = 32 ->
  scan_ready_z sentence len i.
Proof.
  unfold scan_ready_z.
  auto.
Qed.

Lemma scan_ready_z_step_space : forall sentence len i,
  scan_ready_z sentence len i ->
  Znth i (sentence ++ [0]) 0 = 32 ->
  scan_ready_z sentence len (i + 1).
Proof.
  unfold scan_ready_z.
  intros sentence len i _ Hspace.
  right; right; right.
  replace (i + 1 - 1) with i by lia.
  exact Hspace.
Qed.

Lemma scan_ready_z_nonspace_start : forall sentence len i,
  scan_ready_z sentence len i ->
  i < len ->
  Znth i (sentence ++ [0]) 0 <> 32 ->
  word_start_z sentence i.
Proof.
  unfold scan_ready_z, word_start_z.
  intros sentence len i [Hzero | [Hend | [Hspace | Hprev]]] Hlt Hnonspace.
  - left. exact Hzero.
  - lia.
  - contradiction.
  - right. exact Hprev.
Qed.

Lemma word_copy_prefix_z_step : forall sentence start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength sentence ->
  word_copy_prefix_z start (k + 1) sentence =
  word_copy_prefix_z start k sentence ++
  [Znth (start + k) (sentence ++ [0]) 0].
Proof.
  intros sentence start k Hstart Hk Hbound.
  unfold word_copy_prefix_z.
  rewrite <- app_assoc.
  f_equal.
  replace (start + (k + 1)) with (start + k + 1) by lia.
  assert (0 <= start <= start + k) as Hlo by lia.
  assert (start + k <= start + k + 1 <= Z.of_nat (List.length sentence)) as Hhi.
  { rewrite <- Zlength_correct. lia. }
  rewrite (sublist_split start (start + k + 1) (start + k) sentence Hlo Hhi).
  rewrite (sublist_single (start + k) sentence 0) by (rewrite <- Zlength_correct; lia).
  rewrite app_Znth1 by lia.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma word_copy_prefix_z_0_nonempty : forall sentence start,
  Zlength (words_in_sentence_prefix_z start sentence) > 0 ->
  word_copy_prefix_z start 0 sentence =
  words_in_sentence_prefix_z start sentence ++ [32].
Proof.
  intros sentence start Hlen.
  unfold word_copy_prefix_z.
  destruct (Z.eqb_spec (Zlength (words_in_sentence_prefix_z start sentence)) 0) as [Heq | Hneq].
  - lia.
  - simpl.
  rewrite sublist_nil by lia.
  reflexivity.
Qed.

Lemma word_copy_prefix_z_0_empty : forall sentence start,
  Zlength (words_in_sentence_prefix_z start sentence) <= 0 ->
  word_copy_prefix_z start 0 sentence =
  words_in_sentence_prefix_z start sentence.
Proof.
  intros sentence start Hlen.
  assert (Zlength (words_in_sentence_prefix_z start sentence) = 0).
  { pose proof Zlength_nonneg (words_in_sentence_prefix_z start sentence). lia. }
  unfold word_copy_prefix_z.
  rewrite H.
  simpl.
  rewrite sublist_nil by lia.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma has_divisor_from_true_iff : forall n d,
  has_divisor_from n d = true <->
    exists x, (2 <= x <= d)%nat /\ (n mod x = 0)%nat.
Proof.
  intros n d.
  induction d as [| d IH].
  - cbn [has_divisor_from]. split; [discriminate | intros [x [[Hle Hle'] _]]; lia].
  - destruct d as [| d].
    + cbn [has_divisor_from]. split; [discriminate | intros [x [[Hle Hle'] _]]; lia].
    + cbn [has_divisor_from].
      destruct ((n mod S (S d)) =? 0)%nat eqn:Hmod.
      * split.
        { intro Htrue. exists (S (S d)). split; [lia | apply Nat.eqb_eq; exact Hmod]. }
        { intro Hexists. reflexivity. }
      * rewrite IH.
        split.
        { intros [x [[Hlo Hhi] Hx]].
          exists x. split; [lia | exact Hx]. }
        { intros [x [[Hlo Hhi] Hx]].
          assert (x = S (S d) \/ x <= S d)%nat as [-> | Hlt] by lia.
          - rewrite Hx in Hmod. discriminate.
          - exists x. split; [lia | exact Hx]. }
Qed.

Lemma prime_len_flag_z_composite : forall n,
  2 <= n ->
  (exists d, 2 <= d < n /\ Z.rem n d = 0) ->
  prime_len_flag_z n = 0.
Proof.
  intros n Hn [d [[Hdlo Hdhi] Hrem]].
  unfold prime_len_flag_z, is_prime_bool.
  remember (Z.to_nat n) as m eqn:Hm.
  destruct m as [| [| m]]; [lia | lia |].
  change ((if negb (has_divisor_from (S (S m)) (S m)) then 1 else 0) = 0).
  assert (has_divisor_from (S (S m)) (S m) = true) as Hdiv.
  { apply has_divisor_from_true_iff.
    exists (Z.to_nat d).
    split.
    - lia.
    - rewrite <- Nat2Z.inj_iff.
      rewrite Nat2Z.inj_mod.
      rewrite Hm.
      rewrite !Z2Nat.id by lia.
      rewrite Z.rem_mod_nonneg in Hrem by lia.
      exact Hrem. }
  rewrite Hdiv.
  reflexivity.
Qed.

Lemma prime_len_flag_z_prime : forall n,
  2 <= n ->
  (forall d, 2 <= d < n -> Z.rem n d <> 0) ->
  prime_len_flag_z n = 1.
Proof.
  intros n Hn Hnodiv.
  unfold prime_len_flag_z, is_prime_bool.
  remember (Z.to_nat n) as m eqn:Hm.
  destruct m as [| [| m]]; [lia | lia |].
  change ((if negb (has_divisor_from (S (S m)) (S m)) then 1 else 0) = 1).
  destruct (has_divisor_from (S (S m)) (S m)) eqn:Hdiv; [| reflexivity].
  apply has_divisor_from_true_iff in Hdiv.
  destruct Hdiv as [x [[Hxlo Hxhi] Hmod]].
  specialize (Hnodiv (Z.of_nat x)).
  assert (2 <= Z.of_nat x < n) by lia.
  specialize (Hnodiv H).
  rewrite <- Nat2Z.inj_iff in Hmod.
  rewrite Nat2Z.inj_mod in Hmod.
  rewrite Hm in Hmod.
  rewrite Z2Nat.id in Hmod by lia.
  rewrite Z.rem_mod_nonneg in Hnodiv by lia.
  contradiction.
Qed.

Lemma prime_loop_state_z_flag_0 : forall n j,
  2 <= n ->
  n <= j ->
  j <= n ->
  prime_loop_state_z n j 1 ->
  prime_len_flag_z n = 0.
Proof.
  intros n j Hn Hjn Hjn' Hstate.
  apply prime_len_flag_z_composite; [exact Hn |].
  unfold prime_loop_state_z in Hstate.
  destruct Hstate as [Hto _].
  destruct (Hto eq_refl) as [d [[Hdlo Hdj] Hrem]].
  exists d. split; [lia | exact Hrem].
Qed.

Lemma prime_loop_state_z_flag_1 : forall n j,
  2 <= n ->
  n <= j ->
  j <= n ->
  prime_loop_state_z n j 0 ->
  prime_len_flag_z n = 1.
Proof.
  intros n j Hn Hjn Hjn' Hstate.
  apply prime_len_flag_z_prime; [exact Hn |].
  intros d Hd.
  unfold prime_loop_state_z in Hstate.
  destruct Hstate as [_ Hfrom].
  intro Hrem.
  assert (0 = 1) by (apply Hfrom; exists d; split; [lia | exact Hrem]).
  discriminate.
Qed.

Lemma words_in_sentence_prefix_z_0 : forall sentence,
  words_in_sentence_prefix_z 0 sentence = [].
Proof.
  intros sentence.
  unfold words_in_sentence_prefix_z.
  unfold sublist.
  simpl.
  simpl.
  reflexivity.
Qed.

Lemma string_of_list_z_list_z_of_string : forall s,
  string_of_list_z (list_z_of_string s) = s.
Proof.
  induction s as [| c rest IH]; simpl.
  - reflexivity.
  - unfold z_of_ascii, ascii_of_z.
    rewrite Nat2Z.id, ascii_nat_embedding, IH.
    reflexivity.
Qed.

Lemma ascii_eqb_space_z : forall z,
  0 <= z <= 127 ->
  Ascii.eqb (ascii_of_z z) " "%char = Z.eqb z 32.
Proof.
  intros z Hz.
  destruct (Z.eqb_spec z 32) as [-> | Hneq].
  - reflexivity.
  - apply Ascii.eqb_neq.
    intro Heq.
    apply Hneq.
    assert (nat_of_ascii (ascii_of_z z) = nat_of_ascii " "%char) as Hnat by congruence.
    rewrite nat_of_ascii_ascii_of_z in Hnat by lia.
    change (nat_of_ascii " "%char) with 32%nat in Hnat.
    lia.
Qed.

Lemma split_words_z_aux_ascii : forall cur rest,
  ascii_range_z rest ->
  split_words_ascii_aux (map ascii_of_z cur) (map ascii_of_z rest) =
  map (map ascii_of_z) (split_words_z_aux cur rest).
Proof.
  intros cur rest Hrange.
  revert cur Hrange.
  induction rest as [| h t IH]; intros cur Hrange; simpl.
  - destruct cur as [| z cur]; simpl.
    + reflexivity.
    + rewrite <- map_rev. rewrite map_app. reflexivity.
  - assert (Hh : 0 <= h <= 127).
    {
      assert (0 <= 0 < Zlength (h :: t)) as H0.
      { rewrite Zlength_cons. pose proof Zlength_nonneg t. lia. }
      specialize (Hrange 0 H0). simpl in Hrange. exact Hrange.
    }
    rewrite ascii_eqb_space_z by exact Hh.
    assert (Htail : ascii_range_z t).
    {
      intros i Hi.
      specialize (Hrange (i + 1)).
      assert (0 <= i + 1 < Zlength (h :: t)) as Hi' by (rewrite Zlength_cons; lia).
      specialize (Hrange Hi').
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      exact Hrange.
    }
    destruct (Z.eqb h 32); destruct cur as [| z cur]; simpl.
    + change (@nil ascii) with (map ascii_of_z (@nil Z)).
      apply (IH [] Htail).
    + f_equal.
      * rewrite <- map_rev. rewrite map_app. reflexivity.
      * change (@nil ascii) with (map ascii_of_z (@nil Z)).
        apply (IH [] Htail).
    + change [ascii_of_z h] with (map ascii_of_z [h]).
      apply (IH [h] Htail).
    + change (ascii_of_z h :: ascii_of_z z :: map ascii_of_z cur)
        with (map ascii_of_z (h :: z :: cur)).
      apply (IH (h :: z :: cur) Htail).
Qed.

Lemma split_words_z_ascii : forall sentence,
  ascii_range_z sentence ->
  split_words (map ascii_of_z sentence) =
  map (map ascii_of_z) (split_words_z sentence).
Proof.
  intros sentence Hrange.
  rewrite split_words_eq_spec_aux.
  rewrite split_words_spec_aux_eq.
  unfold split_words_z.
  change (@nil ascii) with (map ascii_of_z (@nil Z)).
  apply split_words_z_aux_ascii.
  exact Hrange.
Qed.

Lemma filter_prime_ascii_z : forall words,
  List.filter (fun w : list ascii => is_prime_bool (Datatypes.length w))
    (map (map ascii_of_z) words) =
  map (map ascii_of_z)
    (List.filter (fun w : list Z => Z.eqb (prime_len_flag_z (Zlength w)) 1) words).
Proof.
  induction words as [| w rest IH]; simpl.
  - reflexivity.
  - unfold prime_len_flag_z.
    rewrite map_length.
    rewrite Zlength_correct.
    rewrite Nat2Z.id.
    destruct (is_prime_bool (Datatypes.length w)); simpl; rewrite IH; reflexivity.
Qed.

Lemma join_words_z_ascii : forall words,
  join_words (map (map ascii_of_z) words) =
  map ascii_of_z (join_words_z words).
Proof.
  induction words as [| w rest IH]; simpl.
  - reflexivity.
  - destruct rest as [| w2 rest].
    + reflexivity.
    + simpl in IH.
      rewrite !map_app.
      simpl.
      rewrite ascii_of_z_32.
      rewrite IH.
      reflexivity.
Qed.

Lemma string_of_list_z_map_ascii : forall l,
  string_of_list_z l = string_of_list_ascii (map ascii_of_z l).
Proof.
  induction l as [| c rest IH]; simpl; congruence.
Qed.

Lemma words_in_sentence_output_z_spec : forall sentence,
  ascii_range_z sentence ->
  problem_143_spec_z sentence (words_in_sentence_output_z sentence).
Proof.
  intros sentence Hrange.
  unfold problem_143_spec_z.
  unfold problem_143_spec.
  unfold words_in_sentence_impl.
  rewrite string_of_list_z_map_ascii.
  rewrite list_ascii_of_string_string_of_list_z.
  rewrite split_words_z_ascii by exact Hrange.
  rewrite filter_prime_ascii_z.
  unfold words_in_sentence_output_z, selected_words_z.
  rewrite join_words_z_ascii.
  reflexivity.
Qed.

Lemma words_in_sentence_prefix_z_full : forall sentence i,
  i = Zlength sentence ->
  words_in_sentence_prefix_z i sentence = words_in_sentence_output_z sentence.
Proof.
  intros sentence i Hi.
  unfold words_in_sentence_prefix_z, words_in_sentence_output_z.
  rewrite sublist_self by exact Hi.
  reflexivity.
Qed.

Definition nonspace_z_list (w : list Z) : Prop :=
  forall x, In x w -> x <> 32.

Lemma split_words_z_aux_no_space : forall cur w,
  nonspace_z_list w ->
  split_words_z_aux cur w =
  match rev cur ++ w with
  | [] => []
  | word => [word]
  end.
Proof.
  intros cur w Hno.
  revert cur Hno.
  induction w as [| h t IH]; intros cur Hno; simpl.
  - destruct cur as [| z cur]; simpl.
    + reflexivity.
    + rewrite app_nil_r. destruct (rev cur); reflexivity.
  - assert (h <> 32) as Hh by (apply Hno; simpl; auto).
    destruct (Z.eqb_spec h 32) as [Heq | Hneq]; [contradiction |].
    rewrite IH.
    + simpl.
      rewrite <- app_assoc.
      reflexivity.
    + intros x Hx. apply Hno. simpl; auto.
Qed.

Lemma split_words_z_aux_app_space_word : forall cur s w,
  nonspace_z_list w ->
  split_words_z_aux cur (s ++ [32] ++ w) =
  split_words_z_aux cur s ++ split_words_z_aux [] w.
Proof.
  intros cur s w Hno.
  revert cur.
  induction s as [| h t IH]; intros cur; simpl.
  - destruct cur as [| z cur]; simpl.
    + reflexivity.
    + reflexivity.
  - destruct (Z.eqb h 32); destruct cur as [| z cur]; simpl; rewrite IH; reflexivity.
Qed.

Lemma sublist_word_no_space : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_chars_z sentence start i ->
  nonspace_z_list (sublist start i sentence).
Proof.
  unfold nonspace_z_list, word_chars_z.
  intros sentence start i Hbounds Hi Hchars x Hin Hx.
  destruct (In_nth (sublist start i sentence) x 0 Hin) as [n [Hn Hnth]].
  assert (0 <= Z.of_nat n < Zlength (sublist start i sentence)) as Hnz.
  { rewrite Zlength_correct. lia. }
  assert (x = Znth (Z.of_nat n) (sublist start i sentence) 0) as Hxnth.
  {
    unfold Znth.
    rewrite Nat2Z.id.
    symmetry. exact Hnth.
  }
  rewrite Hxnth in Hx.
  rewrite Znth_sublist in Hx;
    [| lia | rewrite Zlength_sublist in Hnz by lia; lia].
  assert (start + Z.of_nat n < Zlength sentence) as Hlt.
  {
    rewrite Zlength_sublist in Hnz by lia.
    lia.
  }
  assert (start <= start + Z.of_nat n < i) as Hp.
  {
    rewrite Zlength_sublist in Hnz by lia.
    lia.
  }
  assert (Znth (start + Z.of_nat n) (sentence ++ [0]) 0 <> 32) as Hneq.
  { apply Hchars. exact Hp. }
  rewrite app_Znth1 in Hneq by lia.
  apply Hneq.
  replace (start + Z.of_nat n) with (Z.of_nat n + start) by lia.
  exact Hx.
Qed.

Lemma sublist_word_start_space : forall sentence start,
  0 < start ->
  start <= Zlength sentence ->
  word_start_z sentence start ->
  sublist 0 start sentence = sublist 0 (start - 1) sentence ++ [32].
Proof.
  intros sentence start Hpos Hbound Hstart.
  unfold word_start_z in Hstart.
  destruct Hstart as [Hzero | Hspace]; [lia |].
  rewrite (sublist_split 0 start (start - 1) sentence);
    [| lia | rewrite <- Zlength_correct; lia].
  assert (sublist (start - 1) start sentence = [Znth (start - 1) sentence 0]) as Hsingle.
  {
    pose proof (sublist_single (start - 1) sentence 0) as Hs.
    rewrite <- Zlength_correct in Hs.
    specialize (Hs ltac:(lia)).
    replace (start - 1 + 1) with start in Hs by lia.
    exact Hs.
  }
  rewrite Hsingle.
  rewrite app_Znth1 in Hspace by lia.
  rewrite Hspace.
  reflexivity.
Qed.

Lemma split_words_z_boundary_word : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start_z sentence start ->
  word_chars_z sentence start i ->
  split_words_z (sublist 0 i sentence) =
  split_words_z (sublist 0 start sentence) ++
  split_words_z (sublist start i sentence).
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars.
  assert (Hno := sublist_word_no_space sentence start i Hbounds Hi Hchars).
  rewrite (sublist_split 0 i start sentence);
    [| lia | rewrite <- Zlength_correct; lia].
  destruct (Z.eq_dec start 0) as [-> | Hnz].
  - rewrite sublist_nil by lia.
    simpl.
    reflexivity.
  - assert (0 < start) by lia.
    rewrite (sublist_word_start_space sentence start) by lia || exact Hstart.
    unfold split_words_z.
    rewrite <- app_assoc.
    rewrite split_words_z_aux_app_space_word by exact Hno.
    rewrite split_words_z_aux_app_space.
    reflexivity.
Qed.

Lemma selected_words_z_boundary_nonprime : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start_z sentence start ->
  word_chars_z sentence start i ->
  prime_len_flag_z (i - start) <> 1 ->
  selected_words_z (sublist 0 i sentence) =
  selected_words_z (sublist 0 start sentence).
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hnonprime.
  unfold selected_words_z.
  rewrite (split_words_z_boundary_word sentence start i) by assumption.
  rewrite List.filter_app.
  assert (Hno := sublist_word_no_space sentence start i Hbounds Hi Hchars).
  replace (split_words_z (sublist start i sentence)) with
    (match sublist start i sentence with [] => [] | word => [word] end).
  2:{
    unfold split_words_z.
    rewrite split_words_z_aux_no_space with (cur := []) by exact Hno.
    reflexivity.
  }
  destruct (sublist start i sentence) as [| h t] eqn:Hword.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl.
    assert (Zlength (h :: t) = i - start) as Hlen.
    {
      rewrite <- Hword.
      rewrite Zlength_sublist by lia.
      reflexivity.
    }
    rewrite Hlen.
    destruct (Z.eqb_spec (prime_len_flag_z (i - start)) 1); [contradiction |].
    simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma prime_len_flag_z_one_nonempty : forall w : list Z,
  Z.eqb (prime_len_flag_z (Zlength w)) 1 = true ->
  w <> [].
Proof.
  intros w Hprime ->.
  unfold prime_len_flag_z in Hprime.
  simpl in Hprime.
  discriminate.
Qed.

Lemma selected_words_z_nonempty : forall words w,
  In w (List.filter (fun w : list Z => Z.eqb (prime_len_flag_z (Zlength w)) 1) words) ->
  w <> [].
Proof.
  intros words w Hin.
  apply List.filter_In in Hin.
  destruct Hin as [_ Hprime].
  apply prime_len_flag_z_one_nonempty.
  exact Hprime.
Qed.

Lemma join_words_z_nonempty : forall ws,
  (forall w, In w ws -> w <> []) ->
  ws <> [] ->
  Zlength (join_words_z ws) > 0.
Proof.
  intros ws Hnonempty Hws.
  destruct ws as [| w rest]; [contradiction |].
  specialize (Hnonempty w ltac:(simpl; auto)).
  destruct w as [| h t]; [contradiction |].
  destruct rest as [| r rs]; simpl; rewrite Zlength_correct; simpl; lia.
Qed.

Lemma join_words_z_app_single : forall ws w,
  (forall word, In word ws -> word <> []) ->
  w <> [] ->
  join_words_z (ws ++ [w]) =
  join_words_z ws ++
  (if Z.eqb (Zlength (join_words_z ws)) 0 then [] else [32]) ++ w.
Proof.
  intros ws w Hws Hw.
  destruct ws as [| a rest].
  - simpl. reflexivity.
  - assert (Zlength (join_words_z (a :: rest)) > 0) as Hlen.
    {
      apply join_words_z_nonempty.
      - intros word Hin. apply Hws. simpl; auto.
      - discriminate.
    }
    destruct (Z.eqb_spec (Zlength (join_words_z (a :: rest))) 0) as [Hz | Hnz]; [lia |].
    clear Hlen Hnz.
    revert a Hws.
    induction rest as [| b rest IH]; intros a Hws; simpl.
    + reflexivity.
    + change (a ++ [32] ++ join_words_z ((b :: rest) ++ [w]) =
              (a ++ [32] ++ join_words_z (b :: rest)) ++ [32] ++ w).
      rewrite IH.
      * rewrite !app_assoc. reflexivity.
      * intros word Hin. apply Hws. simpl; auto.
Qed.

Lemma selected_words_z_boundary_prime : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start_z sentence start ->
  word_chars_z sentence start i ->
  prime_len_flag_z (i - start) = 1 ->
  selected_words_z (sublist 0 i sentence) =
  selected_words_z (sublist 0 start sentence) ++ [sublist start i sentence].
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hprime.
  unfold selected_words_z.
  rewrite (split_words_z_boundary_word sentence start i) by assumption.
  rewrite List.filter_app.
  assert (Hno := sublist_word_no_space sentence start i Hbounds Hi Hchars).
  replace (split_words_z (sublist start i sentence)) with
    (match sublist start i sentence with [] => [] | word => [word] end).
  2:{
    unfold split_words_z.
    rewrite split_words_z_aux_no_space with (cur := []) by exact Hno.
    reflexivity.
  }
  destruct (sublist start i sentence) as [| h t] eqn:Hword.
  - assert (i - start = 0) as Hlen0.
    {
      assert (0 <= start <= i /\ i <= Zlength sentence) as Hb by lia.
      pose proof (Zlength_sublist start i sentence Hb) as Hlen.
      rewrite Hword in Hlen.
      rewrite Zlength_nil in Hlen.
      lia.
    }
    rewrite Hlen0 in Hprime.
    unfold prime_len_flag_z in Hprime.
    simpl in Hprime.
    discriminate.
  - simpl.
    assert (Zlength (h :: t) = i - start) as Hlen.
    {
      rewrite <- Hword.
      rewrite Zlength_sublist by lia.
      reflexivity.
    }
    rewrite Hlen, Hprime.
    simpl.
    reflexivity.
Qed.

Lemma words_in_sentence_prefix_z_nonprime_word : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start_z sentence start ->
  word_chars_z sentence start i ->
  prime_len_flag_z (i - start) <> 1 ->
  words_in_sentence_prefix_z i sentence =
  words_in_sentence_prefix_z start sentence.
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hnonprime.
  unfold words_in_sentence_prefix_z, words_in_sentence_output_z.
  rewrite (selected_words_z_boundary_nonprime sentence start i) by assumption.
  reflexivity.
Qed.

Lemma words_in_sentence_prefix_z_prime_word : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start_z sentence start ->
  word_chars_z sentence start i ->
  prime_len_flag_z (i - start) = 1 ->
  words_in_sentence_prefix_z i sentence =
  word_copy_prefix_z start (i - start) sentence.
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hprime.
  unfold words_in_sentence_prefix_z, words_in_sentence_output_z, word_copy_prefix_z.
  rewrite (selected_words_z_boundary_prime sentence start i) by assumption.
  assert (Hseg_nonempty : sublist start i sentence <> []).
  {
    intro Hnil.
    assert (i - start = 0) as Hlen0.
    {
      assert (0 <= start <= i /\ i <= Zlength sentence) as Hb by lia.
      pose proof (Zlength_sublist start i sentence Hb) as Hlen.
      rewrite Hnil in Hlen.
      rewrite Zlength_nil in Hlen.
      lia.
    }
    rewrite Hlen0 in Hprime.
    unfold prime_len_flag_z in Hprime.
    simpl in Hprime.
    discriminate.
  }
  rewrite join_words_z_app_single.
  - replace (start + (i - start)) with i by lia.
    reflexivity.
  - intros word Hin.
    eapply selected_words_z_nonempty.
    unfold selected_words_z.
    exact Hin.
  - exact Hseg_nonempty.
Qed.

Lemma Zlength_rev_z : forall (l : list Z),
  Zlength (rev l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, List.rev_length.
  reflexivity.
Qed.

Lemma join_words_z_cons_bound : forall w ws,
  Zlength (join_words_z (w :: ws)) <=
  Zlength w + 1 + Zlength (join_words_z ws).
Proof.
  intros w ws.
  destruct ws as [| a rest].
  - simpl. change (Zlength (@nil Z)) with 0. lia.
  - simpl. rewrite !Zlength_app, Zlength_cons. lia.
Qed.

Lemma words_output_z_aux_len_bound : forall cur rest,
  Zlength
    (join_words_z
       (List.filter (fun w : list Z => Z.eqb (prime_len_flag_z (Zlength w)) 1)
          (split_words_z_aux cur rest))) <=
  Zlength cur + Zlength rest.
Proof.
  intros cur rest.
  revert cur.
  induction rest as [| h t IH]; intros cur; simpl.
  - destruct cur as [| z cur].
    + simpl. lia.
    + assert (Zlength (rev (z :: cur)) = Zlength (z :: cur)) as Hrev
        by apply Zlength_rev_z.
      simpl in Hrev.
      simpl.
      rewrite Hrev.
      destruct (Z.eqb (prime_len_flag_z (Zlength (z :: cur))) 1).
      * simpl. change (Zlength (@nil Z)) with 0.
        rewrite Hrev.
        rewrite Z.add_0_r. apply Z.le_refl.
      * simpl. change (Zlength (@nil Z)) with 0. pose proof Zlength_nonneg (z :: cur). lia.
  - destruct (Z.eqb h 32) eqn:Hspace.
    + destruct cur as [| z cur].
      * specialize (IH []).
        simpl in IH.
        eapply Z.le_trans; [exact IH |].
        replace (Zlength [] + Zlength (h :: t)) with (1 + Zlength t)
          by (rewrite Zlength_cons, Zlength_nil; lia).
        pose proof Zlength_nonneg t. lia.
      * destruct (Z.eqb (prime_len_flag_z (Zlength (rev (z :: cur)))) 1) eqn:Hsel.
        -- simpl in Hsel. simpl. rewrite Hsel.
           pose proof (join_words_z_cons_bound (rev (z :: cur))
             (List.filter
                (fun w : list Z => Z.eqb (prime_len_flag_z (Zlength w)) 1)
                (split_words_z_aux [] t))) as Hbound.
           specialize (IH []).
           simpl in IH.
           rewrite Zlength_rev_z in Hbound.
           eapply Z.le_trans; [exact Hbound |].
           replace (Zlength (h :: t)) with (Z.succ (Zlength t))
             by (rewrite Zlength_cons; reflexivity).
           lia.
        -- simpl in Hsel. simpl. rewrite Hsel.
           specialize (IH []).
           simpl in IH.
           eapply Z.le_trans; [exact IH |].
           replace (Zlength (h :: t)) with (Z.succ (Zlength t))
             by (rewrite Zlength_cons; reflexivity).
           pose proof Zlength_nonneg (z :: cur). lia.
    + specialize (IH (h :: cur)).
      simpl in IH.
      replace (Zlength cur + Zlength (h :: t)) with (Zlength (h :: cur) + Zlength t).
      * exact IH.
      * rewrite !Zlength_cons. lia.
Qed.

Lemma words_in_sentence_prefix_z_len_bound : forall sentence i,
  0 <= i <= Zlength sentence ->
  Zlength (words_in_sentence_prefix_z i sentence) <= i.
Proof.
  intros sentence i Hi.
  unfold words_in_sentence_prefix_z, words_in_sentence_output_z, selected_words_z, split_words_z.
  pose proof (words_output_z_aux_len_bound [] (sublist 0 i sentence)) as Hbound.
  simpl in Hbound.
  rewrite Zlength_sublist0 in Hbound by lia.
  exact Hbound.
Qed.
