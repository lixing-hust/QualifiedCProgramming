Load "../spec/103".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_103 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_103 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_103 c) (string_of_list_z_103 rest)
  end.

Definition problem_103_pre_z (n m : Z) : Prop :=
  problem_103_pre n m.

Definition problem_103_spec_z (n m : Z) (output : list Z) : Prop :=
  problem_103_spec n m (string_of_list_z_103 output).

Fixpoint positive_bits_103 (p : positive) : list Z :=
  match p with
  | xH => [1]
  | xO q => 0 :: positive_bits_103 q
  | xI q => 1 :: positive_bits_103 q
  end.

Definition binary_bits_pos_z_103 (n : Z) : list Z :=
  match n with
  | Zpos p => positive_bits_103 p
  | _ => []
  end.

Definition binary_bits_z_103 (n : Z) : list Z :=
  match n with
  | Z0 => [0]
  | Zpos p => positive_bits_103 p
  | Zneg _ => []
  end.

Definition bit_code_z_103 (b : Z) : Z := 48 + b.

Definition binary_output_z_103 (n : Z) : list Z :=
  map bit_code_z_103 (rev (binary_bits_z_103 n)).

Definition binary_length_z_103 (n : Z) : Z :=
  Zlength (binary_output_z_103 n).

Definition binary_count_state_z_103 (orig x bits : Z) : Prop :=
  0 <= x /\
  0 <= bits /\
  bits + Zlength (binary_bits_pos_z_103 x) =
    Zlength (binary_bits_pos_z_103 orig).

Definition binary_backfill_state_z_103
    (orig rem pos : Z) (suffix : list Z) : Prop :=
  exists done,
    0 < orig /\
    0 <= rem <= orig /\
    0 <= pos <= binary_length_z_103 orig /\
    binary_bits_pos_z_103 orig = done ++ binary_bits_pos_z_103 rem /\
    pos = binary_length_z_103 orig - Zlength done /\
    suffix = map bit_code_z_103 (rev done) ++ [0].

(* This predicate contains only arithmetic, loop-transition, and allocation
   safety facts for the existing C helper.  The original problem spec is
   connected separately by proved lemmas below. *)
Definition binary_safe_103 (num : Z) : Prop :=
  0 <= num <= INT_MAX /\
  0 < binary_length_z_103 num + 1 < INT_MAX /\
  binary_output_z_103 0 = [48] /\
  binary_count_state_z_103 num num 0 /\
  (forall x bits,
      binary_count_state_z_103 num x bits ->
      0 < x ->
      binary_count_state_z_103 num (Z.quot x 2) (bits + 1)) /\
  (forall bits,
      0 < num ->
      binary_count_state_z_103 num 0 bits ->
      bits = binary_length_z_103 num) /\
  (forall bits,
      0 < num ->
      bits = binary_length_z_103 num ->
      1 <= bits) /\
  (forall bits,
      0 < num ->
      bits = binary_length_z_103 num ->
      binary_backfill_state_z_103 num num bits [0]) /\
  (forall rem pos suffix,
      binary_backfill_state_z_103 num rem pos suffix ->
      0 < rem ->
      0 < pos /\
      0 <= 48 + Z.rem rem 2 <= 127 /\
      binary_backfill_state_z_103
        num (Z.quot rem 2) (pos - 1)
        ((48 + Z.rem rem 2) :: suffix)) /\
  (forall suffix,
      binary_backfill_state_z_103 num 0 0 suffix ->
      suffix = binary_output_z_103 num ++ [0]).

Definition rounded_avg_safe_103 (n m : Z) : Prop :=
  n <= m ->
  let avg := Z.quot (n + m) 2 in
  0 < avg <= INT_MAX /\
  Z.quot (n + m) 2 = (n + m) / 2 /\
  binary_safe_103 avg.

Lemma binary_safe_length_bound_103 : forall n,
  binary_safe_103 n ->
  0 < binary_length_z_103 n + 1 < INT_MAX.
Proof. intros n H; unfold binary_safe_103 in H; tauto. Qed.

Lemma binary_safe_count_initial_103 : forall n,
  binary_safe_103 n ->
  binary_count_state_z_103 n n 0.
Proof. intros n H; unfold binary_safe_103 in H; tauto. Qed.

Lemma binary_safe_count_step_103 : forall n x bits,
  binary_safe_103 n ->
  binary_count_state_z_103 n x bits ->
  0 < x ->
  binary_count_state_z_103 n (Z.quot x 2) (bits + 1).
Proof.
  intros n x bits Hsafe Hstate Hpos.
  unfold binary_safe_103 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [Hstep _]]]]].
  apply Hstep; assumption.
Qed.

Lemma binary_safe_count_final_103 : forall n bits,
  binary_safe_103 n ->
  0 < n ->
  binary_count_state_z_103 n 0 bits ->
  bits = binary_length_z_103 n.
Proof.
  intros n bits Hsafe Hpos Hstate.
  unfold binary_safe_103 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [Hfinal _]]]]]].
  apply Hfinal; assumption.
Qed.

Lemma binary_safe_length_pos_103 : forall n bits,
  binary_safe_103 n ->
  0 < n ->
  bits = binary_length_z_103 n ->
  1 <= bits.
Proof.
  intros n bits Hsafe Hpos Hbits.
  unfold binary_safe_103 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [Hlen _]]]]]]].
  apply Hlen; assumption.
Qed.

Lemma binary_safe_backfill_initial_103 : forall n bits,
  binary_safe_103 n ->
  0 < n ->
  bits = binary_length_z_103 n ->
  binary_backfill_state_z_103 n n bits [0].
Proof.
  intros n bits Hsafe Hpos Hbits.
  unfold binary_safe_103 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [Hinit _]]]]]]]].
  apply Hinit; assumption.
Qed.

Lemma binary_safe_backfill_step_103 : forall n rem pos suffix,
  binary_safe_103 n ->
  binary_backfill_state_z_103 n rem pos suffix ->
  0 < rem ->
  0 < pos /\
  0 <= 48 + Z.rem rem 2 <= 127 /\
  binary_backfill_state_z_103
    n (Z.quot rem 2) (pos - 1) ((48 + Z.rem rem 2) :: suffix).
Proof.
  intros n rem pos suffix Hsafe Hstate Hpos.
  unfold binary_safe_103 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [Hstep _]]]]]]]]].
  apply Hstep; assumption.
Qed.

Lemma binary_safe_backfill_final_103 : forall n suffix,
  binary_safe_103 n ->
  binary_backfill_state_z_103 n 0 0 suffix ->
  suffix = binary_output_z_103 n ++ [0].
Proof.
  intros n suffix Hsafe Hstate.
  unfold binary_safe_103 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hfinal]]]]]]]]].
  apply Hfinal; assumption.
Qed.

Lemma binary_backfill_zero_pos_103 : forall n pos suffix,
  binary_backfill_state_z_103 n 0 pos suffix ->
  pos = 0.
Proof.
  intros n pos suffix Hstate.
  unfold binary_backfill_state_z_103 in Hstate.
  destruct Hstate as (done & Hnpos & _ & _ & Hbits & Hpos & _).
  simpl in Hbits. rewrite app_nil_r in Hbits. subst done.
  unfold binary_length_z_103, binary_output_z_103 in Hpos.
  destruct n as [|p|p]; try lia; simpl in *.
  rewrite !Zlength_correct, length_map, length_rev in Hpos.
  lia.
Qed.

Lemma binary_safe_zero_output_103 : forall n,
  binary_safe_103 n ->
  n = 0 ->
  binary_output_z_103 n = [48].
Proof.
  intros n H ->. unfold binary_safe_103 in H. tauto.
Qed.

Lemma rounded_avg_safe_use_103 : forall n m,
  rounded_avg_safe_103 n m ->
  n <= m ->
  let avg := Z.quot (n + m) 2 in
  0 < avg <= INT_MAX /\
  avg = (n + m) / 2 /\
  binary_safe_103 avg.
Proof.
  intros n m Hsafe Hle. unfold rounded_avg_safe_103 in Hsafe.
  apply Hsafe; assumption.
Qed.

Lemma positive_bits_nonempty_103 : forall p,
  positive_bits_103 p <> [].
Proof.
  destruct p; discriminate.
Qed.

Lemma positive_bits_bound_103 : forall p,
  list_within_bound 2 (positive_bits_103 p).
Proof.
  induction p; simpl; intuition lia.
Qed.

Lemma positive_bits_value_103 : forall p,
  list_to_Z 2 (positive_bits_103 p) = Z.pos p.
Proof.
  induction p; simpl [positive_bits_103].
  - rewrite list_to_Z_cons, IHp. rewrite Pos2Z.inj_xI. lia.
  - rewrite list_to_Z_cons, IHp. rewrite Pos2Z.inj_xO. lia.
  - rewrite list_to_Z_single. reflexivity.
Qed.

Lemma positive_bits_last_103 : forall p,
  last (positive_bits_103 p) 0 = 1.
Proof.
  induction p as [p IH | p IH |].
  - simpl [positive_bits_103].
    destruct (positive_bits_103 p) eqn:Hbits.
    + exfalso. apply (positive_bits_nonempty_103 p). assumption.
    + exact IH.
  - simpl [positive_bits_103].
    destruct (positive_bits_103 p) eqn:Hbits.
    + exfalso. apply (positive_bits_nonempty_103 p). assumption.
    + exact IH.
  - reflexivity.
Qed.

Lemma binary_bits_values_103 : forall n,
  0 <= n ->
  Forall (fun b => b = 0 \/ b = 1) (binary_bits_z_103 n).
Proof.
  intros n Hn.
  destruct n as [|p|p]; try lia; simpl.
  - constructor; [left; reflexivity | constructor].
  - induction p; simpl; constructor; intuition.
Qed.

Lemma binary_bits_rel_103 : forall n,
  0 <= n ->
  binary_digits (Z.to_nat n) (binary_bits_z_103 n).
Proof.
  intros n Hn.
  destruct n as [|p|p]; try lia.
  - unfold binary_digits, binary_bits_z_103; simpl.
    rewrite list_to_Z_single. repeat split; auto.
  - unfold binary_digits, binary_bits_z_103; simpl.
    split; [apply positive_bits_bound_103 |].
    split.
    + rewrite positive_bits_value_103. symmetry. apply positive_nat_Z.
    + right. repeat split.
      * pose proof (Pos2Nat.is_pos p). lia.
      * apply positive_bits_nonempty_103.
      * apply positive_bits_last_103.
Qed.

Lemma string_of_list_z_bit_codes_103 : forall bits,
  Forall (fun b => b = 0 \/ b = 1) bits ->
  string_of_list_z_103 (map bit_code_z_103 bits) =
  string_of_list_ascii (map bit_char bits).
Proof.
  intros bits Hbits.
  induction Hbits as [|b bits Hb Hbits IH]; simpl.
  - reflexivity.
  - destruct Hb as [-> | ->]; simpl; rewrite IH; reflexivity.
Qed.

Lemma binary_output_string_103 : forall n,
  0 <= n ->
  string_of_list_z_103 (binary_output_z_103 n) =
  binary_string_from_digits (binary_bits_z_103 n).
Proof.
  intros n Hn.
  unfold binary_output_z_103, binary_string_from_digits.
  apply string_of_list_z_bit_codes_103.
  apply Forall_rev.
  apply binary_bits_values_103; assumption.
Qed.

Lemma problem_103_spec_z_neg : forall n m,
  n > m ->
  problem_103_spec_z n m [45; 49].
Proof.
  intros n m Hgt.
  unfold problem_103_spec_z, problem_103_spec.
  left. split; [assumption | reflexivity].
Qed.

Lemma problem_103_spec_z_binary : forall n m avg,
  n <= m ->
  0 <= avg ->
  avg = (n + m) / 2 ->
  problem_103_spec_z n m (binary_output_z_103 avg).
Proof.
  intros n m avg Hle Havg Hvalue.
  unfold problem_103_spec_z, problem_103_spec.
  right.
  exists (Z.to_nat avg), (binary_bits_z_103 avg).
  split; [exact Hle |].
  split.
  - rewrite Z2Nat.id by lia. exact Hvalue.
  - split.
    + apply binary_bits_rel_103; assumption.
    + apply binary_output_string_103; assumption.
Qed.
