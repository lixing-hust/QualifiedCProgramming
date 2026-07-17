Load "../spec/95".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.
Load "../StringClaude/string_bridge".

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition row_payload_z_95 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition rows_to_dictionary_z_95 (rows : list (list Z)) : dictionary :=
  map
    (fun row =>
       (Some (string_of_list_z (row_payload_z_95 row)), EmptyString))
    rows.

Definition problem_95_pre_z (rows : list (list Z)) : Prop :=
  problem_95_pre (rows_to_dictionary_z_95 rows).

Definition problem_95_spec_z (rows : list (list Z)) (ret : Z) : Prop :=
  problem_95_spec (rows_to_dictionary_z_95 rows) (bool_of_z ret).

Definition lower_char_z_95 (c : Z) : Prop := 97 <= c <= 122.
Definition upper_char_z_95 (c : Z) : Prop := 65 <= c <= 90.
Definition letter_char_z_95 (c : Z) : Prop :=
  lower_char_z_95 c \/ upper_char_z_95 c.

Definition row_char_bound_z_95 (row : list Z) (i : Z) : Prop :=
  0 <= i < Zlength row - 1.

Definition rows_well_formed_z_95
    (rows : list (list Z)) (dict_size : Z) : Prop :=
  Zlength rows = dict_size /\
  forall k,
    0 <= k < dict_size ->
    0 < Zlength (Znth k rows []) <= 101 /\
    Znth (Zlength (Znth k rows []) - 1) (Znth k rows []) 0 = 0 /\
    all_ascii (Znth k rows []) /\
    forall i,
      row_char_bound_z_95 (Znth k rows []) i ->
      Znth i (Znth k rows []) 0 <> 0.

Definition processed_char_bound_z_95
    (k i : Z) (rows : list (list Z)) (r j : Z) : Prop :=
  0 <= r < Zlength rows /\
  row_char_bound_z_95 (Znth r rows []) j /\
  ((0 <= r < k) \/ (r = k /\ 0 <= j < i)).

Definition processed_all_letters_z_95
    (k i : Z) (rows : list (list Z)) : Prop :=
  forall r j,
    processed_char_bound_z_95 k i rows r j ->
    letter_char_z_95 (Znth j (Znth r rows []) 0).

Definition processed_has_lower_z_95
    (k i : Z) (rows : list (list Z)) : Prop :=
  exists r j,
    processed_char_bound_z_95 k i rows r j /\
    lower_char_z_95 (Znth j (Znth r rows []) 0).

Definition processed_has_upper_z_95
    (k i : Z) (rows : list (list Z)) : Prop :=
  exists r j,
    processed_char_bound_z_95 k i rows r j /\
    upper_char_z_95 (Znth j (Znth r rows []) 0).

Definition dict_case_state_z_95
    (k i : Z) (rows : list (list Z)) (islower isupper : Z) : Prop :=
  processed_all_letters_z_95 k i rows /\
  (islower = 1 <-> processed_has_lower_z_95 k i rows) /\
  (isupper = 1 <-> processed_has_upper_z_95 k i rows) /\
  0 <= islower <= 1 /\
  0 <= isupper <= 1 /\
  islower + isupper <= 1.

Definition rows_all_lower_z_95 (rows : list (list Z)) : Prop :=
  forall r j,
    0 <= r < Zlength rows ->
    row_char_bound_z_95 (Znth r rows []) j ->
    lower_char_z_95 (Znth j (Znth r rows []) 0).

Definition rows_all_upper_z_95 (rows : list (list Z)) : Prop :=
  forall r j,
    0 <= r < Zlength rows ->
    row_char_bound_z_95 (Znth r rows []) j ->
    upper_char_z_95 (Znth j (Znth r rows []) 0).

Lemma problem_95_pre_z_true : forall rows, problem_95_pre_z rows.
Proof.
  intros rows. unfold problem_95_pre_z, problem_95_pre. exact I.
Qed.

Lemma rows_well_formed_length_95 : forall rows n,
  rows_well_formed_z_95 rows n -> Zlength rows = n.
Proof. intros rows n [H _]. exact H. Qed.

Lemma rows_well_formed_row_95 : forall rows n k,
  rows_well_formed_z_95 rows n ->
  0 <= k < n ->
  0 < Zlength (Znth k rows []) <= 101 /\
  Znth (Zlength (Znth k rows []) - 1) (Znth k rows []) 0 = 0 /\
  all_ascii (Znth k rows []) /\
  forall i,
    row_char_bound_z_95 (Znth k rows []) i ->
    Znth i (Znth k rows []) 0 <> 0.
Proof. intros rows n k [_ H]. now apply H. Qed.

Lemma processed_char_bound_step_95 : forall rows k i r j,
  0 <= k < Zlength rows ->
  row_char_bound_z_95 (Znth k rows []) i ->
  (processed_char_bound_z_95 k (i + 1) rows r j <->
   processed_char_bound_z_95 k i rows r j \/ (r = k /\ j = i)).
Proof.
  intros rows k i r j Hk Hi.
  unfold processed_char_bound_z_95, row_char_bound_z_95 in *.
  split.
  - intros [Hr [Hj [Hbefore | Hcurrent]]].
    + left. exact (conj Hr (conj Hj (or_introl Hbefore))).
    + destruct Hcurrent as [Hr_eq Hj_range]. subst r.
      destruct (Z_lt_ge_dec j i) as [Hji | Hji].
      * left. split; [exact Hk |]. split; [exact Hj |].
        right. split; [reflexivity | lia].
      * right. lia.
  - intros [[Hr [Hj Hpos]] | [Hr_eq Hj_eq]].
    + split; [exact Hr |]. split; [exact Hj |].
      destruct Hpos as [Hbefore | [Hr_eq Hj_range]].
      * now left.
      * right. split; [exact Hr_eq | lia].
    + subst r j. split; [exact Hk |]. split; [exact Hi |].
      right. split; [reflexivity | lia].
Qed.

Lemma dict_case_state_init_95 : forall rows,
  dict_case_state_z_95 0 0 rows 0 0.
Proof.
  intros rows.
  unfold dict_case_state_z_95, processed_all_letters_z_95,
    processed_has_lower_z_95, processed_has_upper_z_95,
    processed_char_bound_z_95.
  repeat split; try lia; intros; firstorder lia.
Qed.

Lemma dict_case_state_lower_step_95 : forall rows k i islower isupper,
  0 <= k < Zlength rows ->
  row_char_bound_z_95 (Znth k rows []) i ->
  lower_char_z_95 (Znth i (Znth k rows []) 0) ->
  isupper + 1 <> 2 ->
  dict_case_state_z_95 k i rows islower isupper ->
  dict_case_state_z_95 k (i + 1) rows 1 isupper.
Proof.
  intros rows k i islower isupper Hk Hi Hlower Hsum Hstate.
  destruct Hstate as [Hall [Hlower_flag [Hupper_flag [Hlr [Hur Hle]]]]].
  unfold dict_case_state_z_95.
  split.
  - intros r j Hprocessed.
    apply processed_char_bound_step_95 in Hprocessed; auto.
    destruct Hprocessed as [Hold | [-> ->]].
    + now apply Hall with (r := r) (j := j).
    + now left.
  - split.
    + split; intros _.
      * exists k, i. split; [|exact Hlower].
        apply (proj2 (processed_char_bound_step_95 rows k i k i Hk Hi)).
        now right.
      * reflexivity.
    + split.
      * split.
        -- intros Hu.
           apply Hupper_flag in Hu.
           destruct Hu as [r [j [Hbound Hchar]]].
           exists r, j. split; [|exact Hchar].
           apply (proj2 (processed_char_bound_step_95 rows k i r j Hk Hi)).
           now left.
        -- intros [r [j [Hbound Hchar]]].
           apply processed_char_bound_step_95 in Hbound; auto.
           destruct Hbound as [Hold | [Hr Hj]].
           ++ apply Hupper_flag. exists r, j. now split.
           ++ subst r j. unfold lower_char_z_95, upper_char_z_95 in *. lia.
      * split; [lia|]. split; [exact Hur|lia].
Qed.

Lemma dict_case_state_upper_step_95 : forall rows k i islower isupper,
  0 <= k < Zlength rows ->
  row_char_bound_z_95 (Znth k rows []) i ->
  upper_char_z_95 (Znth i (Znth k rows []) 0) ->
  1 + islower <> 2 ->
  dict_case_state_z_95 k i rows islower isupper ->
  dict_case_state_z_95 k (i + 1) rows islower 1.
Proof.
  intros rows k i islower isupper Hk Hi Hupper Hsum Hstate.
  destruct Hstate as [Hall [Hlower_flag [Hupper_flag [Hlr [Hur Hle]]]]].
  unfold dict_case_state_z_95.
  split.
  - intros r j Hprocessed.
    apply processed_char_bound_step_95 in Hprocessed; auto.
    destruct Hprocessed as [Hold | [-> ->]].
    + now apply Hall with (r := r) (j := j).
    + now right.
  - split.
    + split.
      * intros Hl.
        apply Hlower_flag in Hl.
        destruct Hl as [r [j [Hbound Hchar]]].
        exists r, j. split; [|exact Hchar].
        apply (proj2 (processed_char_bound_step_95 rows k i r j Hk Hi)).
        now left.
      * intros [r [j [Hbound Hchar]]].
        apply processed_char_bound_step_95 in Hbound; auto.
        destruct Hbound as [Hold | [Hr Hj]].
        -- apply Hlower_flag. exists r, j. now split.
        -- subst r j. unfold lower_char_z_95, upper_char_z_95 in *. lia.
    + split.
      * split; intros _.
        -- exists k, i. split; [|exact Hupper].
           apply (proj2 (processed_char_bound_step_95 rows k i k i Hk Hi)).
           now right.
        -- reflexivity.
      * split; [exact Hlr|]. split; [lia|lia].
Qed.

Lemma current_nonzero_before_last_95 : forall rows n k i,
  rows_well_formed_z_95 rows n ->
  0 <= k < n ->
  0 <= i < Zlength (Znth k rows []) ->
  Znth i (Znth k rows []) 0 <> 0 ->
  row_char_bound_z_95 (Znth k rows []) i /\
  i + 1 < Zlength (Znth k rows []).
Proof.
  intros rows n k i Hwf Hk Hi Hnonzero.
  pose proof (rows_well_formed_row_95 rows n k Hwf Hk) as
    [_ [Hlast [_ Hinner]]].
  unfold row_char_bound_z_95.
  assert (i <> Zlength (Znth k rows []) - 1) by congruence.
  split; lia.
Qed.

Lemma current_zero_is_last_95 : forall rows n k i,
  rows_well_formed_z_95 rows n ->
  0 <= k < n ->
  0 <= i < Zlength (Znth k rows []) ->
  Znth i (Znth k rows []) 0 = 0 ->
  i = Zlength (Znth k rows []) - 1.
Proof.
  intros rows n k i Hwf Hk Hi Hz.
  pose proof (rows_well_formed_row_95 rows n k Hwf Hk) as
    [_ [_ [_ Hinner]]].
  destruct (Z_lt_ge_dec i (Zlength (Znth k rows []) - 1)).
  - exfalso. apply (Hinner i); [unfold row_char_bound_z_95; lia|]. congruence.
  - lia.
Qed.

Lemma processed_char_bound_row_done_95 : forall rows k i r j,
  0 <= k < Zlength rows ->
  i = Zlength (Znth k rows []) - 1 ->
  (processed_char_bound_z_95 (k + 1) 0 rows r j <->
   processed_char_bound_z_95 k i rows r j).
Proof.
  intros rows k i r j Hk Hi.
  unfold processed_char_bound_z_95, row_char_bound_z_95 in *.
  split.
  - intros [Hr [Hj [Hbefore | [Hr_eq Hj_range]]]].
    + split; [exact Hr |]. split; [exact Hj |].
      destruct (Z.lt_trichotomy r k) as [Hlt | [Heq | Hgt]].
      * now left.
      * subst r. right. split; [reflexivity | lia].
      * lia.
    + lia.
  - intros [Hr [Hj [Hbefore | [Hr_eq Hj_range]]]].
    + split; [exact Hr |]. split; [exact Hj |]. left. lia.
    + split; [exact Hr |]. split; [exact Hj |]. left. lia.
Qed.

Lemma dict_case_state_row_done_95 : forall rows n k i islower isupper,
  rows_well_formed_z_95 rows n ->
  0 <= k < n ->
  0 <= i < Zlength (Znth k rows []) ->
  Znth i (Znth k rows []) 0 = 0 ->
  dict_case_state_z_95 k i rows islower isupper ->
  dict_case_state_z_95 (k + 1) 0 rows islower isupper.
Proof.
  intros rows n k i islower isupper Hwf Hk Hi Hz Hstate.
  pose proof (rows_well_formed_length_95 rows n Hwf) as Hlen.
  pose proof (current_zero_is_last_95 rows n k i Hwf Hk Hi Hz) as Hilast.
  destruct Hstate as [Hall [Hlower [Hupper Hranges]]].
  unfold dict_case_state_z_95.
  split.
  - intros r j Hb. apply Hall with (r := r) (j := j).
    pose proof (processed_char_bound_row_done_95 rows k i r j ltac:(lia) Hilast) as Heq.
    exact (proj1 Heq Hb).
  - split.
    + split.
      * intros Hflag. apply Hlower in Hflag.
        destruct Hflag as [r [j [Hb Hc]]]. exists r, j. split; [|exact Hc].
        pose proof (processed_char_bound_row_done_95 rows k i r j ltac:(lia) Hilast) as Heq.
        exact (proj2 Heq Hb).
      * intros [r [j [Hb Hc]]]. apply Hlower. exists r, j. split; [|exact Hc].
        pose proof (processed_char_bound_row_done_95 rows k i r j ltac:(lia) Hilast) as Heq.
        exact (proj1 Heq Hb).
    + split.
      * split.
        -- intros Hflag. apply Hupper in Hflag.
           destruct Hflag as [r [j [Hb Hc]]]. exists r, j. split; [|exact Hc].
           pose proof (processed_char_bound_row_done_95 rows k i r j ltac:(lia) Hilast) as Heq.
           exact (proj2 Heq Hb).
        -- intros [r [j [Hb Hc]]]. apply Hupper. exists r, j. split; [|exact Hc].
           pose proof (processed_char_bound_row_done_95 rows k i r j ltac:(lia) Hilast) as Heq.
           exact (proj1 Heq Hb).
      * exact Hranges.
Qed.

Lemma ascii_leb_nat_iff_95 : forall a b,
  (a <=? b)%char = true <-> (nat_of_ascii a <= nat_of_ascii b)%nat.
Proof.
  intros a b.
  unfold Ascii.leb, Ascii.compare, nat_of_ascii.
  destruct (N.compare_spec (N_of_ascii a) (N_of_ascii b)) as [Heq | Hlt | Hgt].
  - subst. simpl. lia.
  - simpl. zify. lia.
  - simpl. split; [discriminate|].
    intro Hle. zify. lia.
Qed.

Lemma lower_ascii_z_95 : forall z,
  0 <= z < 256 ->
  (lower_char_z_95 z <->
   (("a" <=? ascii_of_z z)%char && (ascii_of_z z <=? "z")%char) = true).
Proof.
  intros z Hz.
  unfold lower_char_z_95.
  rewrite Bool.andb_true_iff, !ascii_leb_nat_iff_95.
  rewrite nat_of_ascii_ascii_of_z by exact Hz.
  change (97 <= z <= 122 <->
          (97 <= Z.to_nat z)%nat /\ (Z.to_nat z <= 122)%nat).
  rewrite <- (Z2Nat.inj_le 97 z) by lia.
  rewrite <- (Z2Nat.inj_le z 122) by lia.
  tauto.
Qed.

Lemma upper_ascii_z_95 : forall z,
  0 <= z < 256 ->
  (upper_char_z_95 z <->
   (("A" <=? ascii_of_z z)%char && (ascii_of_z z <=? "Z")%char) = true).
Proof.
  intros z Hz.
  unfold upper_char_z_95.
  rewrite Bool.andb_true_iff, !ascii_leb_nat_iff_95.
  rewrite nat_of_ascii_ascii_of_z by exact Hz.
  change (65 <= z <= 90 <->
          (65 <= Z.to_nat z)%nat /\ (Z.to_nat z <= 90)%nat).
  rewrite <- (Z2Nat.inj_le 65 z) by lia.
  rewrite <- (Z2Nat.inj_le z 90) by lia.
  tauto.
Qed.

Lemma row_payload_length_95 : forall row,
  0 < Zlength row ->
  Zlength (row_payload_z_95 row) = Zlength row - 1.
Proof.
  intros row Hlen.
  unfold row_payload_z_95.
  rewrite Zlength_correct, length_firstn.
  rewrite Zlength_correct in Hlen |- *.
  replace (Z.to_nat (Z.of_nat (Datatypes.length row) - 1))
    with (Datatypes.length row - 1)%nat by lia.
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma row_payload_Znth_95 : forall row i,
  0 <= i < Zlength row - 1 ->
  Znth i (row_payload_z_95 row) 0 = Znth i row 0.
Proof.
  intros row i Hi.
  unfold row_payload_z_95, Znth.
  rewrite nth_firstn by lia.
  reflexivity.
Qed.

Lemma row_payload_index_in_95 : forall row i,
  0 <= i < Zlength row - 1 ->
  In (Znth i row 0) (row_payload_z_95 row).
Proof.
  intros row i Hi.
  rewrite <- row_payload_Znth_95 by exact Hi.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct, row_payload_length_95 by lia.
  lia.
Qed.

Lemma row_payload_in_index_95 : forall row c,
  0 < Zlength row ->
  In c (row_payload_z_95 row) ->
  exists i,
    0 <= i < Zlength row - 1 /\ Znth i row 0 = c.
Proof.
  intros row c Hlen Hin.
  destruct (In_nth (row_payload_z_95 row) c 0 Hin) as [n [Hn Hnth]].
  apply Nat2Z.inj_lt in Hn.
  rewrite <- Zlength_correct in Hn.
  rewrite row_payload_length_95 in Hn by exact Hlen.
  exists (Z.of_nat n).
  split.
  - lia.
  - rewrite <- row_payload_Znth_95.
    + unfold Znth. rewrite Nat2Z.id. exact Hnth.
    + lia.
Qed.

Lemma row_lower_to_is_lowercase_95 : forall row,
  0 < Zlength row ->
  (forall j,
      row_char_bound_z_95 row j -> lower_char_z_95 (Znth j row 0)) ->
  is_lowercase (string_of_list_z (row_payload_z_95 row)).
Proof.
  intros row Hlen Hlower.
  unfold is_lowercase.
  rewrite list_ascii_of_string_string_of_list_z.
  apply Forall_forall. intros a Ha.
  apply in_map_iff in Ha.
  destruct Ha as [c [<- Hc]].
  destruct (row_payload_in_index_95 row c Hlen Hc) as [j [Hj Heq]].
  subst c.
  apply lower_ascii_z_95.
  - unfold lower_char_z_95 in Hlower. specialize (Hlower j Hj). lia.
  - now apply Hlower.
Qed.

Lemma row_upper_to_is_uppercase_95 : forall row,
  0 < Zlength row ->
  (forall j,
      row_char_bound_z_95 row j -> upper_char_z_95 (Znth j row 0)) ->
  is_uppercase (string_of_list_z (row_payload_z_95 row)).
Proof.
  intros row Hlen Hupper.
  unfold is_uppercase.
  rewrite list_ascii_of_string_string_of_list_z.
  apply Forall_forall. intros a Ha.
  apply in_map_iff in Ha.
  destruct Ha as [c [<- Hc]].
  destruct (row_payload_in_index_95 row c Hlen Hc) as [j [Hj Heq]].
  subst c.
  apply upper_ascii_z_95.
  - unfold upper_char_z_95 in Hupper. specialize (Hupper j Hj). lia.
  - now apply Hupper.
Qed.

Lemma is_lowercase_to_row_lower_95 : forall row,
  0 < Zlength row ->
  all_ascii row ->
  is_lowercase (string_of_list_z (row_payload_z_95 row)) ->
  forall j,
    row_char_bound_z_95 row j -> lower_char_z_95 (Znth j row 0).
Proof.
  intros row Hlen Hascii Hlower j Hj.
  unfold is_lowercase in Hlower.
  rewrite list_ascii_of_string_string_of_list_z in Hlower.
  apply Forall_forall with (x := ascii_of_z (Znth j row 0)) in Hlower.
  - assert (0 <= Znth j row 0 < 256) as Hrange.
    { pose proof (Hascii j ltac:(unfold row_char_bound_z_95 in Hj; lia)) as Hc.
      lia. }
    exact (proj2 (lower_ascii_z_95 (Znth j row 0) Hrange) Hlower).
  - apply in_map. now apply row_payload_index_in_95.
Qed.

Lemma is_uppercase_to_row_upper_95 : forall row,
  0 < Zlength row ->
  all_ascii row ->
  is_uppercase (string_of_list_z (row_payload_z_95 row)) ->
  forall j,
    row_char_bound_z_95 row j -> upper_char_z_95 (Znth j row 0).
Proof.
  intros row Hlen Hascii Hupper j Hj.
  unfold is_uppercase in Hupper.
  rewrite list_ascii_of_string_string_of_list_z in Hupper.
  apply Forall_forall with (x := ascii_of_z (Znth j row 0)) in Hupper.
  - assert (0 <= Znth j row 0 < 256) as Hrange.
    { pose proof (Hascii j ltac:(unfold row_char_bound_z_95 in Hj; lia)) as Hc.
      lia. }
    exact (proj2 (upper_ascii_z_95 (Znth j row 0) Hrange) Hupper).
  - apply in_map. now apply row_payload_index_in_95.
Qed.

Definition dictionary_all_lower_95 (d : dictionary) : Prop :=
  forall k v,
    In (k, v) d -> exists s, k = Some s /\ is_lowercase s.

Definition dictionary_all_upper_95 (d : dictionary) : Prop :=
  forall k v,
    In (k, v) d -> exists s, k = Some s /\ is_uppercase s.

Lemma rows_index_in_95 : forall (rows : list (list Z)) r,
  0 <= r < Zlength rows -> In (Znth r rows []) rows.
Proof.
  intros rows r Hr. unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma row_in_rows_index_95 : forall (rows : list (list Z)) row,
  In row rows ->
  exists r, 0 <= r < Zlength rows /\ Znth r rows [] = row.
Proof.
  intros rows row Hin.
  destruct (In_nth rows row [] Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n). split.
  - apply Nat2Z.inj_lt in Hn. rewrite <- Zlength_correct in Hn. lia.
  - unfold Znth. now rewrite Nat2Z.id.
Qed.

Lemma dictionary_lower_rows_iff_95 : forall rows n,
  rows_well_formed_z_95 rows n ->
  (dictionary_all_lower_95 (rows_to_dictionary_z_95 rows) <->
   rows_all_lower_z_95 rows).
Proof.
  intros rows n Hwf. split.
  - intros Hdict r j Hr Hj.
    pose proof (rows_well_formed_length_95 rows n Hwf) as Hlen.
    pose proof (rows_well_formed_row_95 rows n r Hwf ltac:(lia)) as
      [Hrowlen [_ [Hascii Hnonzero]]].
    unfold dictionary_all_lower_95 in Hdict.
    specialize (Hdict
      (Some (string_of_list_z (row_payload_z_95 (Znth r rows []))))
      EmptyString).
    assert (In
      (Some (string_of_list_z (row_payload_z_95 (Znth r rows []))), EmptyString)
      (rows_to_dictionary_z_95 rows)) as Hin.
    { unfold rows_to_dictionary_z_95. apply in_map_iff.
      exists (Znth r rows []). split; [reflexivity|].
      now apply rows_index_in_95. }
    specialize (Hdict Hin).
    destruct Hdict as [s [Hs Hlower]]. inversion Hs; subst s.
    now apply (is_lowercase_to_row_lower_95 (Znth r rows []) ltac:(lia) Hascii Hlower j).
  - intros Hrows k v Hin.
    unfold rows_to_dictionary_z_95 in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [row [Hpair Hinrow]].
    inversion Hpair; subst k v.
    destruct (row_in_rows_index_95 rows row Hinrow) as [r [Hr Hrow]].
    exists (string_of_list_z (row_payload_z_95 row)). split; [reflexivity|].
    pose proof (rows_well_formed_length_95 rows n Hwf) as Hlen.
    pose proof (rows_well_formed_row_95 rows n r Hwf ltac:(lia)) as
      [Hrowlen _].
    apply row_lower_to_is_lowercase_95; [rewrite <- Hrow; lia|].
    intros j Hj. rewrite <- Hrow.
    apply Hrows with (r := r) (j := j); [exact Hr|].
    now rewrite Hrow.
Qed.

Lemma dictionary_upper_rows_iff_95 : forall rows n,
  rows_well_formed_z_95 rows n ->
  (dictionary_all_upper_95 (rows_to_dictionary_z_95 rows) <->
   rows_all_upper_z_95 rows).
Proof.
  intros rows n Hwf. split.
  - intros Hdict r j Hr Hj.
    pose proof (rows_well_formed_length_95 rows n Hwf) as Hlen.
    pose proof (rows_well_formed_row_95 rows n r Hwf ltac:(lia)) as
      [Hrowlen [_ [Hascii Hnonzero]]].
    unfold dictionary_all_upper_95 in Hdict.
    specialize (Hdict
      (Some (string_of_list_z (row_payload_z_95 (Znth r rows []))))
      EmptyString).
    assert (In
      (Some (string_of_list_z (row_payload_z_95 (Znth r rows []))), EmptyString)
      (rows_to_dictionary_z_95 rows)) as Hin.
    { unfold rows_to_dictionary_z_95. apply in_map_iff.
      exists (Znth r rows []). split; [reflexivity|].
      now apply rows_index_in_95. }
    specialize (Hdict Hin).
    destruct Hdict as [s [Hs Hupper]]. inversion Hs; subst s.
    now apply (is_uppercase_to_row_upper_95 (Znth r rows []) ltac:(lia) Hascii Hupper j).
  - intros Hrows k v Hin.
    unfold rows_to_dictionary_z_95 in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [row [Hpair Hinrow]].
    inversion Hpair; subst k v.
    destruct (row_in_rows_index_95 rows row Hinrow) as [r [Hr Hrow]].
    exists (string_of_list_z (row_payload_z_95 row)). split; [reflexivity|].
    pose proof (rows_well_formed_length_95 rows n Hwf) as Hlen.
    pose proof (rows_well_formed_row_95 rows n r Hwf ltac:(lia)) as
      [Hrowlen _].
    apply row_upper_to_is_uppercase_95; [rewrite <- Hrow; lia|].
    intros j Hj. rewrite <- Hrow.
    apply Hrows with (r := r) (j := j); [exact Hr|].
    now rewrite Hrow.
Qed.

Lemma rows_to_dictionary_nonempty_95 : forall rows,
  rows_to_dictionary_z_95 rows <> [] <-> rows <> [].
Proof.
  intros rows. unfold rows_to_dictionary_z_95.
  destruct rows; simpl; intuition congruence.
Qed.

Lemma uniform_case_rows_iff_95 : forall rows n,
  rows_well_formed_z_95 rows n ->
  (has_uniform_key_case (rows_to_dictionary_z_95 rows) <->
   rows <> [] /\ (rows_all_lower_z_95 rows \/ rows_all_upper_z_95 rows)).
Proof.
  intros rows n Hwf.
  unfold has_uniform_key_case.
  change
    (rows_to_dictionary_z_95 rows <> [] /\
       (dictionary_all_lower_95 (rows_to_dictionary_z_95 rows) \/
        dictionary_all_upper_95 (rows_to_dictionary_z_95 rows)) <->
     rows <> [] /\ (rows_all_lower_z_95 rows \/ rows_all_upper_z_95 rows)).
  rewrite rows_to_dictionary_nonempty_95.
  rewrite (dictionary_lower_rows_iff_95 rows n Hwf).
  rewrite (dictionary_upper_rows_iff_95 rows n Hwf).
  tauto.
Qed.

Lemma problem_95_spec_z_one_iff_95 : forall rows n,
  rows_well_formed_z_95 rows n ->
  (problem_95_spec_z rows 1 <->
   rows <> [] /\ (rows_all_lower_z_95 rows \/ rows_all_upper_z_95 rows)).
Proof.
  intros rows n Hwf.
  unfold problem_95_spec_z, problem_95_spec, bool_of_z.
  cbn.
  rewrite (uniform_case_rows_iff_95 rows n Hwf). intuition congruence.
Qed.

Lemma problem_95_spec_z_zero_iff_95 : forall rows n,
  rows_well_formed_z_95 rows n ->
  (problem_95_spec_z rows 0 <->
   ~ (rows <> [] /\ (rows_all_lower_z_95 rows \/ rows_all_upper_z_95 rows))).
Proof.
  intros rows n Hwf.
  unfold problem_95_spec_z, problem_95_spec, bool_of_z.
  cbn.
  rewrite (uniform_case_rows_iff_95 rows n Hwf). intuition congruence.
Qed.

Lemma dict_case_state_final_uniform_95 : forall rows n islower isupper,
  rows_well_formed_z_95 rows n ->
  0 < n ->
  dict_case_state_z_95 n 0 rows islower isupper ->
  rows <> [] /\ (rows_all_lower_z_95 rows \/ rows_all_upper_z_95 rows).
Proof.
  intros rows n islower isupper Hwf Hn Hstate.
  pose proof (rows_well_formed_length_95 rows n Hwf) as Hlen.
  destruct Hstate as [Hall [Hlower [Hupper [Hlr [Hur Hsum]]]]].
  split.
  - intros Hnil. subst rows. rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct (Z.eq_dec isupper 0) as [Hu0 | Hu0].
    + left. intros r j Hr Hj.
      specialize (Hall r j).
      assert (processed_char_bound_z_95 n 0 rows r j) as Hb.
      { unfold processed_char_bound_z_95.
        split; [exact Hr |]. split; [exact Hj |].
        left. rewrite <- Hlen. exact Hr. }
      specialize (Hall Hb). destruct Hall as [Hl | Hu]; [exact Hl|].
      exfalso.
      assert (processed_has_upper_z_95 n 0 rows) as Hhas.
      { exists r, j. now split. }
      pose proof (proj2 Hupper Hhas). lia.
    + assert (isupper = 1) as Hu1 by lia.
      right. intros r j Hr Hj.
      specialize (Hall r j).
      assert (processed_char_bound_z_95 n 0 rows r j) as Hb.
      { unfold processed_char_bound_z_95.
        split; [exact Hr |]. split; [exact Hj |].
        left. rewrite <- Hlen. exact Hr. }
      specialize (Hall Hb). destruct Hall as [Hl | Hu]; [|exact Hu].
      exfalso.
      assert (processed_has_lower_z_95 n 0 rows) as Hhas.
      { exists r, j. now split. }
      pose proof (proj2 Hlower Hhas). lia.
Qed.

Lemma problem_95_spec_z_one_from_state_95 : forall rows n islower isupper,
  rows_well_formed_z_95 rows n ->
  0 < n ->
  dict_case_state_z_95 n 0 rows islower isupper ->
  problem_95_spec_z rows 1.
Proof.
  intros rows n islower isupper Hwf Hn Hstate.
  apply (proj2 (problem_95_spec_z_one_iff_95 rows n Hwf)).
  exact (dict_case_state_final_uniform_95 rows n islower isupper
           Hwf Hn Hstate).
Qed.

Lemma problem_95_spec_z_zero_empty_95 : forall rows n,
  rows_well_formed_z_95 rows n -> n = 0 -> problem_95_spec_z rows 0.
Proof.
  intros rows n Hwf ->.
  apply (proj2 (problem_95_spec_z_zero_iff_95 rows 0 Hwf)).
  intros [Hnonempty _].
  pose proof (rows_well_formed_length_95 rows 0 Hwf) as Hlen.
  destruct rows as [|row rows']; [contradiction |].
  rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
Qed.

Lemma problem_95_spec_z_zero_invalid_95 : forall rows n k i islower isupper,
  rows_well_formed_z_95 rows n ->
  0 <= k < n ->
  0 <= i < Zlength (Znth k rows []) ->
  Znth i (Znth k rows []) 0 <> 0 ->
  ~ letter_char_z_95 (Znth i (Znth k rows []) 0) ->
  dict_case_state_z_95 k i rows islower isupper ->
  problem_95_spec_z rows 0.
Proof.
  intros rows n k i islower isupper Hwf Hk Hi Hnonzero Hnotletter Hstate.
  destruct (current_nonzero_before_last_95 rows n k i Hwf Hk Hi Hnonzero) as [Hib _].
  apply (proj2 (problem_95_spec_z_zero_iff_95 rows n Hwf)).
  intros [_ [Halllower | Hallupper]].
  - apply Hnotletter. left.
    apply Halllower with (r := k) (j := i); [|exact Hib].
    rewrite (rows_well_formed_length_95 rows n Hwf). exact Hk.
  - apply Hnotletter. right.
    apply Hallupper with (r := k) (j := i); [|exact Hib].
    rewrite (rows_well_formed_length_95 rows n Hwf). exact Hk.
Qed.

Lemma problem_95_spec_z_zero_lower_mixed_95 : forall rows n k i islower isupper,
  rows_well_formed_z_95 rows n ->
  0 <= k < n ->
  row_char_bound_z_95 (Znth k rows []) i ->
  lower_char_z_95 (Znth i (Znth k rows []) 0) ->
  isupper + 1 = 2 ->
  dict_case_state_z_95 k i rows islower isupper ->
  problem_95_spec_z rows 0.
Proof.
  intros rows n k i islower isupper Hwf Hk Hib Hcur Hsum Hstate.
  destruct Hstate as [Hall [Hlower [Hupper Hranges]]].
  assert (isupper = 1) by lia.
  apply Hupper in H.
  destruct H as [r [j [Hb Hupperchar]]].
  apply (proj2 (problem_95_spec_z_zero_iff_95 rows n Hwf)).
  intros [_ [Halllower | Hallupper]].
  - pose proof Hb as [Hr [Hjb Hpos]].
    specialize (Halllower r j Hr Hjb).
    unfold lower_char_z_95, upper_char_z_95 in *. lia.
  - specialize (Hallupper k i ltac:(pose proof (rows_well_formed_length_95 rows n Hwf); lia) Hib).
    unfold lower_char_z_95, upper_char_z_95 in *. lia.
Qed.

Lemma problem_95_spec_z_zero_upper_mixed_95 : forall rows n k i islower isupper,
  rows_well_formed_z_95 rows n ->
  0 <= k < n ->
  row_char_bound_z_95 (Znth k rows []) i ->
  upper_char_z_95 (Znth i (Znth k rows []) 0) ->
  1 + islower = 2 ->
  dict_case_state_z_95 k i rows islower isupper ->
  problem_95_spec_z rows 0.
Proof.
  intros rows n k i islower isupper Hwf Hk Hib Hcur Hsum Hstate.
  destruct Hstate as [Hall [Hlower [Hupper Hranges]]].
  assert (islower = 1) by lia.
  apply Hlower in H.
  destruct H as [r [j [Hb Hlowerchar]]].
  apply (proj2 (problem_95_spec_z_zero_iff_95 rows n Hwf)).
  intros [_ [Halllower | Hallupper]].
  - specialize (Halllower k i ltac:(pose proof (rows_well_formed_length_95 rows n Hwf); lia) Hib).
    unfold lower_char_z_95, upper_char_z_95 in *. lia.
  - pose proof Hb as [Hr [Hjb Hpos]].
    specialize (Hallupper r j Hr Hjb).
    unfold lower_char_z_95, upper_char_z_95 in *. lia.
Qed.
