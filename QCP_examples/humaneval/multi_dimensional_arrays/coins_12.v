Load "../spec/12".

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
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_12 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_12 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_12 c) (string_of_list_z_12 rest)
  end.

Definition row_payload_z_12 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_12 (row : list Z) : string :=
  string_of_list_z_12 (row_payload_z_12 row).

Definition rows_to_strings_z_12 (rows : list (list Z)) : list string :=
  map row_string_z_12 rows.

Definition row_len_z_12 (row : list Z) : Z :=
  string_length (row_payload_z_12 row).

Definition problem_12_pre_z (rows : list (list Z)) : Prop :=
  problem_12_pre (rows_to_strings_z_12 rows).

Definition problem_12_spec_none_z (rows : list (list Z)) : Prop :=
  problem_12_spec (rows_to_strings_z_12 rows) None.

Definition problem_12_spec_some_z (rows : list (list Z)) (best_idx : Z) : Prop :=
  problem_12_spec
    (rows_to_strings_z_12 rows)
    (Some (row_string_z_12 (Znth best_idx rows nil))).

Definition rows_well_formed_12 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_12 row in
    row = c_string payload /\
    valid_string payload /\
    string_length payload < INT_MAX.

Definition longest_prefix_z_12
    (rows : list (list Z)) (k best_idx best_len : Z) : Prop :=
  0 <= k <= Zlength rows /\
  ((k = 0 /\ best_idx = -1 /\ best_len = -1) \/
   (0 < k /\
    0 <= best_idx < k /\
    best_len = row_len_z_12 (Znth best_idx rows nil) /\
    (forall j,
       0 <= j < k ->
       row_len_z_12 (Znth j rows nil) <= best_len) /\
    (forall j,
       0 <= j < best_idx ->
       row_len_z_12 (Znth j rows nil) < best_len))).

Lemma String_length_string_of_list_z_12 : forall l,
  String.length (string_of_list_z_12 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_12 : forall row,
  Z.of_nat (String.length (row_string_z_12 row)) = row_len_z_12 row.
Proof.
  intros row.
  unfold row_string_z_12, row_len_z_12, string_length.
  rewrite String_length_string_of_list_z_12.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma problem_12_spec_none_z_intro : forall rows,
  Zlength rows = 0 ->
  problem_12_spec_none_z rows.
Proof.
  intros rows Hlen.
  unfold problem_12_spec_none_z, rows_to_strings_z_12.
  left.
  split; [| reflexivity].
  apply Zlength_nil_inv in Hlen.
  subst; reflexivity.
Qed.

Lemma longest_prefix_z_12_initial : forall rows,
  longest_prefix_z_12 rows 0 (-1) (-1).
Proof.
  intros rows.
  unfold longest_prefix_z_12.
  split; [rewrite Zlength_correct; lia|].
  left; auto.
Qed.

Lemma longest_prefix_z_12_nonempty_bounds : forall rows k best_idx best_len,
  longest_prefix_z_12 rows k best_idx best_len ->
  0 < k ->
  0 <= best_idx < k.
Proof.
  intros rows k best_idx best_len Hpref Hk.
  unfold longest_prefix_z_12 in Hpref.
  destruct Hpref as [_ [[Hz _] | [_ [Hb _]]]]; lia.
Qed.

Lemma nth_error_Znth_12 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  nth_error l (Z.to_nat i) = Some (Znth i l d).
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_error_nth'.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma longest_prefix_z_12_step_update : forall rows k best_idx best_len len,
  longest_prefix_z_12 rows k best_idx best_len ->
  0 <= k < Zlength rows ->
  len = row_len_z_12 (Znth k rows nil) ->
  best_len < len ->
  longest_prefix_z_12 rows (k + 1) k len.
Proof.
  intros rows k best_idx best_len len Hpref Hk Hlen Hgt.
  unfold longest_prefix_z_12 in *.
  destruct Hpref as [Hkbounds Hcase].
  split; [lia|].
  right.
  split; [lia|].
  split; [lia|].
  split; [assumption|].
  split.
  - intros j Hj.
    destruct (Z.eq_dec j k) as [-> | Hne].
    + lia.
    + assert (0 <= j < k) by lia.
      destruct Hcase as [[Hz [Hbi Hbest]] | [_ [_ [_ [Hall _]]]]].
      * subst; lia.
      * specialize (Hall j ltac:(lia)); lia.
  - intros j Hj.
    destruct Hcase as [[Hz [Hbi Hbest]] | [_ [_ [_ [Hall _]]]]].
    + subst; lia.
    + specialize (Hall j ltac:(lia)); lia.
Qed.

Lemma longest_prefix_z_12_step_keep : forall rows k best_idx best_len len,
  longest_prefix_z_12 rows k best_idx best_len ->
  0 <= k < Zlength rows ->
  len = row_len_z_12 (Znth k rows nil) ->
  len <= best_len ->
  longest_prefix_z_12 rows (k + 1) best_idx best_len.
Proof.
  intros rows k best_idx best_len len Hpref Hk Hlen Hle.
  unfold longest_prefix_z_12 in *.
  destruct Hpref as [Hkbounds Hcase].
  destruct Hcase as [[Hz [Hbi Hbest]] | [Hkpos [Hb [Hbest [Hall Hfirst]]]]].
  - pose proof (string_length_nonneg (row_payload_z_12 (Znth k rows nil))) as Hnonneg.
    unfold row_len_z_12 in Hlen.
    lia.
  - split; [lia|].
    right.
    split; [lia|].
    split; [lia|].
    split; [assumption|].
    split.
    + intros j Hj.
      destruct (Z.eq_dec j k) as [-> | Hne].
      * lia.
      * apply Hall; lia.
    + intros j Hj.
      apply Hfirst; lia.
Qed.

Lemma longest_prefix_z_12_final_spec : forall rows best_idx best_len,
  rows_well_formed_12 rows (Zlength rows) ->
  problem_12_pre_z rows ->
  0 < Zlength rows ->
  longest_prefix_z_12 rows (Zlength rows) best_idx best_len ->
  problem_12_spec_some_z rows best_idx.
Proof.
  intros rows best_idx best_len _ _ Hnonempty Hpref.
  unfold problem_12_spec_some_z, problem_12_spec.
  right.
  exists (row_string_z_12 (Znth best_idx rows nil)), (Z.to_nat best_idx).
  unfold rows_to_strings_z_12.
  unfold longest_prefix_z_12 in Hpref.
  destruct Hpref as [_ [[Hz _] | [_ [Hb [Hbest [Hall Hfirst]]]]]]; [lia|].
  repeat split; auto.
  - apply Nat2Z.inj_lt.
    rewrite Nat2Z.inj_0, length_map.
    rewrite <- Zlength_correct.
    lia.
  - rewrite length_map.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - rewrite nth_error_map.
    rewrite (nth_error_Znth_12 rows best_idx nil) by lia.
    reflexivity.
  - intros j Hj.
    exists (row_string_z_12 (Znth (Z.of_nat j) rows nil)).
    intros _.
    apply Nat2Z.inj_le.
    rewrite !row_string_length_z_12.
    rewrite <- Hbest.
    apply Hall.
    split; [lia|].
    apply Nat2Z.inj_lt in Hj.
    rewrite length_map in Hj.
    rewrite <- Zlength_correct in Hj.
    lia.
  - intros j Hj.
    exists (row_string_z_12 (Znth (Z.of_nat j) rows nil)).
    intros _.
    apply Nat2Z.inj_lt.
    rewrite !row_string_length_z_12.
    rewrite <- Hbest.
    apply Hfirst.
    split; [lia|].
    apply Nat2Z.inj_lt in Hj.
    rewrite Z2Nat.id in Hj by lia.
    lia.
Qed.

Lemma rows_well_formed_12_row : forall rows n k,
  rows_well_formed_12 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_12 row in
  row = c_string payload /\
  valid_string payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid Hlt]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hlt|].
  subst row payload.
  change (Zlength (Znth k rows nil) =
          Zlength (row_payload_z_12 (Znth k rows nil)) + 1).
  rewrite Hrow at 1.
  unfold c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.
