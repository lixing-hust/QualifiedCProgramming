Load "../spec/64".
Load "../StringClaude/string_bridge".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Parameter LitMap : string -> addr.

Definition problem_64_pre_z (s : list Z) : Prop :=
  problem_64_pre (string_of_list_z s).

Definition problem_64_spec_z (s : list Z) (output : Z) : Prop :=
  problem_64_spec (string_of_list_z s) (Z.to_nat output).

Definition vowel_literal_64 : string := "aeiouAEIOU"%string.

Definition all_vowel_literals_64 : list string :=
  [vowel_literal_64].

Definition vowel_payload_64 : list Z :=
  [97; 101; 105; 111; 117; 65; 69; 73; 79; 85].

Definition vowel_ptr_64 (LM : string -> Z) : Z :=
  LM vowel_literal_64.

Definition vowel_payload_safe_64 : Prop :=
  string_lib.valid_string vowel_payload_64 /\
  all_ascii vowel_payload_64 /\
  string_length vowel_payload_64 < INT_MAX.

Definition vowel_literal_heap_64 (LM : string -> Z) : Assertion :=
  string_lib.store_string (vowel_ptr_64 LM) vowel_payload_64 **
  GlobalStrings_missing LM all_vowel_literals_64.

Definition regular_vowel_code_64 (c : Z) : Prop :=
  c = 97 \/ c = 101 \/ c = 105 \/ c = 111 \/ c = 117 \/
  c = 65 \/ c = 69 \/ c = 73 \/ c = 79 \/ c = 85.

Definition y_code_64 (c : Z) : Prop :=
  c = 121 \/ c = 89.

Definition regular_vowel_codeb_64 (c : Z) : bool :=
  Z.eqb c 97 || Z.eqb c 101 || Z.eqb c 105 || Z.eqb c 111 ||
  Z.eqb c 117 || Z.eqb c 65 || Z.eqb c 69 || Z.eqb c 73 ||
  Z.eqb c 79 || Z.eqb c 85.

Lemma regular_vowel_codeb_spec_64 : forall c,
  regular_vowel_codeb_64 c = true <-> regular_vowel_code_64 c.
Proof.
  intros c. unfold regular_vowel_codeb_64, regular_vowel_code_64.
  repeat rewrite Bool.orb_true_iff.
  repeat rewrite Z.eqb_eq.
  tauto.
Qed.

Definition regular_positions_prefix_64 (s : list Z) (i : Z) : list nat :=
  filter
    (fun k => regular_vowel_codeb_64 (Znth (Z.of_nat k) s 0))
    (seq 0 (Z.to_nat i)).

Definition vowel_count_state_64 (s : list Z) (i count : Z) : Prop :=
  0 <= i <= string_length s /\
  count = Z.of_nat (List.length (regular_positions_prefix_64 s i)).

Definition vowel_regular_step_64 (s : list Z) (i count : Z) : Prop :=
  0 <= i < string_length s /\
  regular_vowel_code_64 (Znth i (c_string s) 0) /\
  vowel_count_state_64 s (i + 1) count.

Definition vowel_miss_step_64 (s : list Z) (i count : Z) : Prop :=
  0 <= i < string_length s /\
  ~ regular_vowel_code_64 (Znth i (c_string s) 0) /\
  vowel_count_state_64 s (i + 1) count.

Definition vowel_final_empty_64 (s : list Z) (count : Z) : Prop :=
  string_length s = 0 /\ count = 0 /\ problem_64_spec_z s count.

Definition vowel_final_y_64 (s : list Z) (count : Z) : Prop :=
  0 < string_length s /\
  y_code_64 (Znth (string_length s - 1) (c_string s) 0) /\
  problem_64_spec_z s count.

Definition vowel_final_not_y_64 (s : list Z) (count : Z) : Prop :=
  0 < string_length s /\
  ~ y_code_64 (Znth (string_length s - 1) (c_string s) 0) /\
  problem_64_spec_z s count.

Lemma vowel_count_initial_64 : forall s,
  vowel_count_state_64 s 0 0.
Proof.
  intros s. unfold vowel_count_state_64, regular_positions_prefix_64.
  split; [unfold string_length; pose proof (Zlength_nonneg s); lia|reflexivity].
Qed.

Lemma vowel_regular_step_intro_64 : forall s i count,
  vowel_count_state_64 s i (count - 1) ->
  0 <= i < string_length s ->
  regular_vowel_code_64 (Znth i (c_string s) 0) ->
  vowel_regular_step_64 s i count.
Proof.
  intros s i count Hstate Hi Hreg.
  unfold vowel_regular_step_64. split; [exact Hi|].
  split; [exact Hreg|].
  unfold vowel_count_state_64 in *. destruct Hstate as [Hbounds Hcount].
  split; [lia|].
  unfold regular_positions_prefix_64 in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S, filter_app, length_app. simpl.
  rewrite c_string_Znth_inside in Hreg by exact Hi.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  apply regular_vowel_codeb_spec_64 in Hreg. rewrite Hreg. simpl.
  rewrite Nat2Z.inj_add. simpl. lia.
Qed.

Lemma vowel_miss_step_intro_64 : forall s i count,
  vowel_count_state_64 s i count ->
  0 <= i < string_length s ->
  ~ regular_vowel_code_64 (Znth i (c_string s) 0) ->
  vowel_miss_step_64 s i count.
Proof.
  intros s i count Hstate Hi Hmiss.
  unfold vowel_miss_step_64. split; [exact Hi|].
  split; [exact Hmiss|].
  unfold vowel_count_state_64 in *. destruct Hstate as [Hbounds Hcount].
  split; [lia|].
  unfold regular_positions_prefix_64 in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S, filter_app, length_app. simpl.
  rewrite c_string_Znth_inside in Hmiss by exact Hi.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  assert (regular_vowel_codeb_64 (Znth i s 0) = false).
  { destruct (regular_vowel_codeb_64 (Znth i s 0)) eqn:Hb; auto.
    apply regular_vowel_codeb_spec_64 in Hb. contradiction. }
  rewrite H. simpl. replace
    (List.length
       (filter
          (fun k : nat => regular_vowel_codeb_64 (Znth (Z.of_nat k) s 0%Z))
          (seq 0 (Z.to_nat i))) + 0)%nat
    with
    (List.length
       (filter
          (fun k : nat => regular_vowel_codeb_64 (Znth (Z.of_nat k) s 0%Z))
          (seq 0 (Z.to_nat i))))%nat by lia.
  exact Hcount.
Qed.

Lemma ascii_of_z_eq_64 : forall x y,
  0 <= x <= 127 -> 0 <= y <= 127 ->
  (ascii_of_z x = ascii_of_z y <-> x = y).
Proof.
  intros x y Hx Hy. split; [intro H|now intros ->].
  apply (f_equal nat_of_ascii) in H.
  rewrite !nat_of_ascii_ascii_of_z in H by lia.
  apply (f_equal Z.of_nat) in H.
  rewrite !Z2Nat.id in H by lia. exact H.
Qed.

Lemma regular_vowel_ascii_code_64 : forall z,
  0 <= z <= 127 ->
  (regular_vowel_64 (ascii_of_z z) <-> regular_vowel_code_64 z).
Proof.
  intros z Hz.
  change
    ((ascii_of_z z = ascii_of_z 97 \/ ascii_of_z z = ascii_of_z 101 \/
      ascii_of_z z = ascii_of_z 105 \/ ascii_of_z z = ascii_of_z 111 \/
      ascii_of_z z = ascii_of_z 117 \/ ascii_of_z z = ascii_of_z 65 \/
      ascii_of_z z = ascii_of_z 69 \/ ascii_of_z z = ascii_of_z 73 \/
      ascii_of_z z = ascii_of_z 79 \/ ascii_of_z z = ascii_of_z 85) <->
     (z = 97 \/ z = 101 \/ z = 105 \/ z = 111 \/ z = 117 \/
      z = 65 \/ z = 69 \/ z = 73 \/ z = 79 \/ z = 85)).
  repeat rewrite (ascii_of_z_eq_64 z) by lia.
  reflexivity.
Qed.

Lemma y_ascii_code_64 : forall z,
  0 <= z <= 127 ->
  ((ascii_of_z z = "y"%char \/ ascii_of_z z = "Y"%char) <-> y_code_64 z).
Proof.
  intros z Hz.
  change
    ((ascii_of_z z = ascii_of_z 121 \/ ascii_of_z z = ascii_of_z 89) <->
     (z = 121 \/ z = 89)).
  repeat rewrite (ascii_of_z_eq_64 z) by lia.
  reflexivity.
Qed.

Lemma nth_error_Znth_64 : forall {A : Type} (l : list A) k d,
  (k < List.length l)%nat ->
  nth_error l k = Some (Znth (Z.of_nat k) l d).
Proof.
  intros A l k d Hk. unfold Znth.
  rewrite Nat2Z.id. apply nth_error_nth'. exact Hk.
Qed.

Lemma nth_error_ascii_Znth_64 : forall s k,
  (k < List.length s)%nat ->
  nth_error (map ascii_of_z s) k =
    Some (ascii_of_z (Znth (Z.of_nat k) s 0)).
Proof.
  intros s k Hk. rewrite nth_error_map.
  rewrite (nth_error_Znth_64 s k 0 Hk). reflexivity.
Qed.

Lemma regular_positions_prefix_In_64 : forall s i k,
  0 <= i ->
  In k (regular_positions_prefix_64 s i) <->
  (k < Z.to_nat i)%nat /\
  regular_vowel_code_64 (Znth (Z.of_nat k) s 0).
Proof.
  intros s i k Hi. unfold regular_positions_prefix_64.
  split.
  - intro Hin. apply filter_In in Hin. destruct Hin as [Hseq Hb].
    apply in_seq in Hseq. split; [lia|].
    apply regular_vowel_codeb_spec_64. exact Hb.
  - intros [Hk Hreg]. apply filter_In. split.
    + apply in_seq. lia.
    + apply regular_vowel_codeb_spec_64. exact Hreg.
Qed.

Lemma counted_vowel_position_code_64 : forall s k,
  all_ascii s ->
  (counted_vowel_position_64 (map ascii_of_z s) k <->
   (k < List.length s)%nat /\
   (regular_vowel_code_64 (Znth (Z.of_nat k) s 0) \/
    (y_code_64 (Znth (Z.of_nat k) s 0) /\ S k = List.length s))).
Proof.
  intros s k Hascii. split.
  - intros [c [Hnth Hkind]].
    assert (Hk : (k < List.length s)%nat).
    { apply nth_error_Some. rewrite nth_error_map in Hnth.
      destruct (nth_error s k); discriminate. }
    rewrite (nth_error_ascii_Znth_64 s k Hk) in Hnth.
    inversion Hnth; subst c.
    assert (Hz : 0 <= Znth (Z.of_nat k) s 0 <= 127).
    { apply Hascii. rewrite Zlength_correct. lia. }
    split; [exact Hk|].
    destruct Hkind as [Hregular | [Hy Hlast]].
    + left. apply (regular_vowel_ascii_code_64 _ Hz). exact Hregular.
    + right. split.
      * apply (y_ascii_code_64 _ Hz). exact Hy.
      * rewrite length_map in Hlast. exact Hlast.
  - intros [Hk Hkind].
    exists (ascii_of_z (Znth (Z.of_nat k) s 0)).
    split; [apply nth_error_ascii_Znth_64; exact Hk|].
    assert (Hz : 0 <= Znth (Z.of_nat k) s 0 <= 127).
    { apply Hascii. rewrite Zlength_correct. lia. }
    destruct Hkind as [Hregular | [Hy Hlast]].
    + left. apply (regular_vowel_ascii_code_64 _ Hz). exact Hregular.
    + right. split.
      * apply (y_ascii_code_64 _ Hz). exact Hy.
      * rewrite length_map. exact Hlast.
Qed.

Lemma regular_positions_full_In_64 : forall s k,
  In k (regular_positions_prefix_64 s (string_length s)) <->
  (k < List.length s)%nat /\
  regular_vowel_code_64 (Znth (Z.of_nat k) s 0).
Proof.
  intros s k. rewrite regular_positions_prefix_In_64.
  - unfold string_length. rewrite Zlength_correct, Nat2Z.id. reflexivity.
  - unfold string_length. apply Zlength_nonneg.
Qed.

Lemma regular_positions_full_NoDup_64 : forall s,
  NoDup (regular_positions_prefix_64 s (string_length s)).
Proof.
  intros s. unfold regular_positions_prefix_64.
  apply NoDup_filter. apply seq_NoDup.
Qed.

Lemma y_code_not_regular_64 : forall z,
  y_code_64 z -> ~ regular_vowel_code_64 z.
Proof.
  intros z Hy. unfold y_code_64, regular_vowel_code_64 in *.
  destruct Hy as [-> | ->]; intuition congruence.
Qed.

Lemma problem_64_spec_regular_64 : forall s count,
  all_ascii s ->
  vowel_count_state_64 s (string_length s) count ->
  (forall k, S k = List.length s ->
     ~ y_code_64 (Znth (Z.of_nat k) s 0)) ->
  problem_64_spec_z s count.
Proof.
  intros s count Hascii Hstate Hnoty.
  unfold vowel_count_state_64 in Hstate. destruct Hstate as [_ Hcount].
  unfold problem_64_spec_z, problem_64_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  exists (regular_positions_prefix_64 s (string_length s)).
  split.
  - split; [apply regular_positions_full_NoDup_64|].
    intros k. rewrite regular_positions_full_In_64.
    rewrite counted_vowel_position_code_64 by exact Hascii.
    split.
    + intros [Hk Hreg]. split; [exact Hk|now left].
    + intros [Hk [Hreg | [Hy Hlast]]]; [now split|].
      exfalso. exact (Hnoty k Hlast Hy).
  - rewrite Hcount. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma vowel_final_empty_intro_64 : forall s count,
  all_ascii s ->
  vowel_count_state_64 s (string_length s) count ->
  string_length s = 0 ->
  vowel_final_empty_64 s count.
Proof.
  intros s count Hascii Hstate Hlen.
  assert (Hcount : count = 0).
  { unfold vowel_count_state_64 in Hstate. destruct Hstate as [_ Hcount].
    unfold regular_positions_prefix_64 in Hcount. rewrite Hlen in Hcount.
    simpl in Hcount. exact Hcount. }
  unfold vowel_final_empty_64. repeat split; try assumption.
  apply problem_64_spec_regular_64; try assumption.
  intros k Hlast. unfold string_length in Hlen.
  rewrite Zlength_correct in Hlen. lia.
Qed.

Lemma vowel_final_not_y_intro_64 : forall s count,
  all_ascii s ->
  vowel_count_state_64 s (string_length s) count ->
  0 < string_length s ->
  ~ y_code_64 (Znth (string_length s - 1) (c_string s) 0) ->
  vowel_final_not_y_64 s count.
Proof.
  intros s count Hascii Hstate Hpos Hnoty.
  unfold vowel_final_not_y_64. repeat split; try assumption.
  apply problem_64_spec_regular_64; try assumption.
  intros k Hlast Hy.
  assert (Hkz : Z.of_nat k = string_length s - 1).
  { unfold string_length. rewrite Zlength_correct. lia. }
  assert (Hy_c : y_code_64 (Znth (Z.of_nat k) (c_string s) 0)).
  { rewrite c_string_Znth_inside; [exact Hy|].
    change (0 <= Z.of_nat k < Zlength s).
    rewrite Zlength_correct. lia. }
  apply Hnoty.
  rewrite <- Hkz. exact Hy_c.
Qed.

Lemma vowel_final_y_intro_64 : forall s count,
  all_ascii s ->
  vowel_count_state_64 s (string_length s) (count - 1) ->
  0 < string_length s ->
  y_code_64 (Znth (string_length s - 1) (c_string s) 0) ->
  vowel_final_y_64 s count.
Proof.
  intros s count Hascii Hstate Hpos Hy_c.
  assert (Hidx : 0 <= string_length s - 1 < string_length s) by lia.
  pose proof Hy_c as Hy_raw.
  rewrite c_string_Znth_inside in Hy_raw by exact Hidx.
  set (last := Z.to_nat (string_length s - 1)).
  set (regular := regular_positions_prefix_64 s (string_length s)).
  assert (Hlast : S last = List.length s).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_succ.
    unfold last. rewrite Z2Nat.id by lia.
    change (Zlength s - 1 + 1 = Z.of_nat (List.length s)).
    rewrite <- Zlength_correct. lia. }
  assert (Hlastz : Z.of_nat last = string_length s - 1).
  { unfold last. rewrite Z2Nat.id by lia. reflexivity. }
  assert (Hlast_notin : ~ In last regular).
  { intro Hin. unfold regular in Hin.
    apply regular_positions_full_In_64 in Hin. destruct Hin as [_ Hreg].
    rewrite Hlastz in Hreg.
    apply (y_code_not_regular_64 _ Hy_raw Hreg). }
  unfold vowel_final_y_64. split; [exact Hpos|].
  split; [exact Hy_c|].
  unfold problem_64_spec_z, problem_64_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  exists (regular ++ [last]). split.
  - split.
    + apply NoDup_app.
      * apply regular_positions_full_NoDup_64.
      * constructor; [simpl; tauto|constructor].
      * intros x Hin Hsingle. simpl in Hsingle.
        destruct Hsingle as [-> | []]. contradiction.
    + intros k. unfold regular. rewrite in_app_iff. simpl.
      rewrite regular_positions_full_In_64.
      rewrite counted_vowel_position_code_64 by exact Hascii.
      split.
      * intros [[Hk Hreg] | [-> | []]].
        -- split; [exact Hk|now left].
        -- split; [lia|right]. split; [rewrite Hlastz; exact Hy_raw|exact Hlast].
      * intros [Hk [Hreg | [Hy Hk_last]]].
        -- left. now split.
        -- right. left. lia.
  - unfold vowel_count_state_64 in Hstate. destruct Hstate as [_ Hcount].
    unfold regular in *. rewrite length_app. simpl.
    replace count with
      (Z.of_nat
         (List.length
            (regular_positions_prefix_64 s (string_length s))) + 1) by lia.
    rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id. simpl. lia.
Qed.

Lemma all_ascii_c_string_inside_64 : forall s i,
  all_ascii s ->
  0 <= i < string_length s ->
  0 <= Znth i (c_string s) 0 <= 127.
Proof.
  intros s i Hascii Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply Hascii.
  unfold string_length in Hi.
  exact Hi.
Qed.

Lemma Znth_In_range_64 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma c_string_nonzero_inside_64 : forall s i,
  string_lib.valid_string s ->
  0 <= i < string_length s ->
  Znth i (c_string s) 0 <> 0.
Proof.
  intros s i Hvalid Hi.
  destruct Hvalid as [_ Hno_nul].
  rewrite c_string_Znth_inside by exact Hi.
  apply Hno_nul.
  unfold string_length in Hi.
  exact Hi.
Qed.

Lemma vowel_lit_to_store_64 : forall LM,
  store_stringLit (LM vowel_literal_64) vowel_literal_64 |--
  string_lib.store_string (vowel_ptr_64 LM) vowel_payload_64.
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold vowel_ptr_64, vowel_payload_64, vowel_literal_64.
  simpl.
  entailer!.
Qed.

Lemma vowel_payload_safe_proof_64 : vowel_payload_safe_64.
Proof.
  unfold vowel_payload_safe_64, string_lib.valid_string, string_lib.all_ascii,
    string_lib.no_inner_nul, all_ascii, no_inner_nul,
    string_length, vowel_payload_64, vowel_literal_64.
  assert (Hascii :
    forall i : Z,
      0 <= i < Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] ->
      0 <= Znth i [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0 <= 127).
  {
    intros i Hi.
    change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
            i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    try change (Znth 0 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 97;
    try change (Znth 1 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 101;
    try change (Znth 2 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 105;
    try change (Znth 3 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 111;
    try change (Znth 4 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 117;
    try change (Znth 5 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 65;
    try change (Znth 6 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 69;
    try change (Znth 7 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 73;
    try change (Znth 8 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 79;
    try change (Znth 9 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 85;
    lia.
  }
  assert (Hlen : Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] < 2147483647) by
    (change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10; lia).
  assert (Hnonzero :
    forall i : Z,
      0 <= i < Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] ->
      Znth i [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0 <> 0).
  {
    intros i Hi.
    pose proof (Hascii i Hi).
    change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
            i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    destruct H0 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    try change (Znth 0 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 97;
    try change (Znth 1 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 101;
    try change (Znth 2 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 105;
    try change (Znth 3 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 111;
    try change (Znth 4 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 117;
    try change (Znth 5 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 65;
    try change (Znth 6 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 69;
    try change (Znth 7 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 73;
    try change (Znth 8 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 79;
    try change (Znth 9 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 85;
    lia.
  }
  split.
  - split; [exact Hascii | exact Hnonzero].
  - split; [exact Hascii | exact Hlen].
Qed.

Lemma vowel_payload_regular_at_64 : forall i c,
  0 <= i < string_length vowel_payload_64 ->
  Znth i vowel_payload_64 0 = c ->
  regular_vowel_code_64 c.
Proof.
  intros i c Hi Hnth.
  unfold vowel_payload_64, vowel_literal_64, string_length in Hi, Hnth.
  change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10 in Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
  try change (Znth 0 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 97 in Hnth;
  try change (Znth 1 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 101 in Hnth;
  try change (Znth 2 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 105 in Hnth;
  try change (Znth 3 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 111 in Hnth;
  try change (Znth 4 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 117 in Hnth;
  try change (Znth 5 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 65 in Hnth;
  try change (Znth 6 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 69 in Hnth;
  try change (Znth 7 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 73 in Hnth;
  try change (Znth 8 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 79 in Hnth;
  try change (Znth 9 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 85 in Hnth;
  subst c;
  unfold regular_vowel_code_64; tauto.
Qed.

Lemma vowel_payload_contains_regular_64 : forall c ret base,
  c <> 0 ->
  strchr_result vowel_payload_64 c ret base ->
  ret <> 0 ->
  regular_vowel_code_64 c.
Proof.
  intros c ret base Hc Hres Hret.
  unfold strchr_result in Hres.
  destruct Hres as [[i [Hi [Hnth [_ [_ _]]]]] |
                    [_ [[Hcz Hret0] | [_ Hret0]]]].
  - eapply vowel_payload_regular_at_64; eauto.
  - contradiction.
  - subst ret. contradiction.
Qed.

Lemma vowel_payload_miss_not_regular_64 : forall c base,
  strchr_result vowel_payload_64 c 0 base ->
  ~ regular_vowel_code_64 c.
Proof.
  intros c base Hres Hreg.
  unfold strchr_result in Hres.
  destruct Hres as [[i [_ [_ [_ [_ Hnz]]]]] |
                    [Hnone _]].
  - contradiction.
  - unfold regular_vowel_code_64 in Hreg.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    end; subst c;
    match goal with
    | |- False =>
        lazymatch goal with
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 97 |- _ =>
            specialize (Hnone 0); apply Hnone;
            [cbv; split; congruence |
             change (Znth 0 vowel_payload_64 0) with 97; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 101 |- _ =>
            specialize (Hnone 1); apply Hnone;
            [cbv; split; congruence |
             change (Znth 1 vowel_payload_64 0) with 101; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 105 |- _ =>
            specialize (Hnone 2); apply Hnone;
            [cbv; split; congruence |
             change (Znth 2 vowel_payload_64 0) with 105; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 111 |- _ =>
            specialize (Hnone 3); apply Hnone;
            [cbv; split; congruence |
             change (Znth 3 vowel_payload_64 0) with 111; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 117 |- _ =>
            specialize (Hnone 4); apply Hnone;
            [cbv; split; congruence |
             change (Znth 4 vowel_payload_64 0) with 117; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 65 |- _ =>
            specialize (Hnone 5); apply Hnone;
            [cbv; split; congruence |
             change (Znth 5 vowel_payload_64 0) with 65; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 69 |- _ =>
            specialize (Hnone 6); apply Hnone;
            [cbv; split; congruence |
             change (Znth 6 vowel_payload_64 0) with 69; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 73 |- _ =>
            specialize (Hnone 7); apply Hnone;
            [cbv; split; congruence |
             change (Znth 7 vowel_payload_64 0) with 73; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 79 |- _ =>
            specialize (Hnone 8); apply Hnone;
            [cbv; split; congruence |
             change (Znth 8 vowel_payload_64 0) with 79; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 85 |- _ =>
            specialize (Hnone 9); apply Hnone;
            [cbv; split; congruence |
             change (Znth 9 vowel_payload_64 0) with 85; reflexivity]
        end
    end.
Qed.
