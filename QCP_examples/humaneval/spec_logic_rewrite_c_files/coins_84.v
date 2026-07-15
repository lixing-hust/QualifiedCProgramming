Load "../spec/84".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition repeat_Z {A : Type} (a : A) (n : Z) : list A :=
  repeat a (Z.to_nat n).

Definition ascii_of_z_84 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_84 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_84 c) (string_of_list_z_84 rest)
  end.

Definition problem_84_pre_z (N : Z) : Prop :=
  problem_84_pre (Z.to_nat N).

Definition problem_84_spec_z (N : Z) (output : list Z) : Prop :=
  problem_84_spec (Z.to_nat N) (string_of_list_z_84 output).

Fixpoint decimal_digit_sum_fuel_84 (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.leb n 0 then 0
      else Z.rem n 10 + decimal_digit_sum_fuel_84 fuel' (Z.quot n 10)
  end.

Definition digit_sum_z_84 (n : Z) : Z :=
  decimal_digit_sum_fuel_84 (Z.to_nat n) n.

Fixpoint binary_bits_fuel_84 (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if Z.leb n 0 then []
      else Z.rem n 2 :: binary_bits_fuel_84 fuel' (Z.quot n 2)
  end.

Definition binary_bits_pos_z_84 (n : Z) : list Z :=
  binary_bits_fuel_84 (Z.to_nat n) n.

Definition binary_bits_z_84 (n : Z) : list Z :=
  if Z.eqb n 0 then [0] else binary_bits_pos_z_84 n.

Definition bit_code_z_84 (b : Z) : Z := 48 + b.

Definition binary_output_z_84 (n : Z) : list Z :=
  map bit_code_z_84 (rev (binary_bits_z_84 n)).

Definition binary_length_z_84 (n : Z) : Z :=
  Zlength (binary_output_z_84 n).

Definition digit_sum_state_z_84 (orig rem sum : Z) : Prop :=
  0 <= rem <= orig /\
  0 <= sum <= 36 /\
  0 <= digit_sum_z_84 orig <= 36 /\
  sum + digit_sum_z_84 rem = digit_sum_z_84 orig /\
  sum + 9 <= INT_MAX /\
  INT_MIN <= sum + 9.

Definition binary_count_state_z_84 (orig x bits : Z) : Prop :=
  0 <= x /\
  0 <= bits /\
  bits + 1 <= INT_MAX /\
  INT_MIN <= bits + 1 /\
  bits + Zlength (binary_bits_pos_z_84 x) =
    Zlength (binary_bits_pos_z_84 orig).

Definition binary_backfill_state_z_84
    (orig rem pos : Z) (suffix : list Z) : Prop :=
  0 < orig /\
  0 <= rem <= orig /\
  0 <= pos <= binary_length_z_84 orig /\
  binary_length_z_84 orig + 1 < INT_MAX /\
  Zlength suffix = binary_length_z_84 orig + 1 - pos /\
  (rem = 0 -> pos = 0) /\
  (forall i, 0 <= i < Zlength suffix -> 0 <= Znth i suffix 0 <= 127).

Definition binary_safe_84 (num : Z) : Prop :=
  0 <= num <= 36 /\
  binary_length_z_84 num + 1 < INT_MAX /\
  binary_output_z_84 0 = [48] /\
  binary_count_state_z_84 num num 0 /\
  (forall x bits,
      binary_count_state_z_84 num x bits ->
      0 < x ->
      binary_count_state_z_84 num (Z.quot x 2) (bits + 1)) /\
  (forall bits,
      0 < num ->
      binary_count_state_z_84 num 0 bits ->
      bits = binary_length_z_84 num) /\
  (forall bits,
      0 < num ->
      bits = binary_length_z_84 num ->
      1 <= bits) /\
  (forall bits,
      0 < num ->
      bits = binary_length_z_84 num ->
      binary_backfill_state_z_84 num num bits [0]) /\
  (forall rem pos suffix,
      binary_backfill_state_z_84 num rem pos suffix ->
      0 < rem ->
      0 < pos /\
      0 <= 48 + Z.rem rem 2 <= 127 /\
      binary_backfill_state_z_84
        num (Z.quot rem 2) (pos - 1) ((48 + Z.rem rem 2) :: suffix)) /\
  (forall suffix,
      binary_backfill_state_z_84 num 0 0 suffix ->
      suffix = binary_output_z_84 num ++ [0]) /\
  (forall out_l,
      out_l = binary_output_z_84 num ->
      Zlength out_l = binary_length_z_84 num).

Definition solve_safe_84 (N : Z) : Prop :=
  0 <= N <= 10000 /\
  digit_sum_state_z_84 N N 0 /\
  (forall rem sum,
      digit_sum_state_z_84 N rem sum ->
      0 < rem ->
      0 <= sum + Z.rem rem 10 <= 36 /\
      digit_sum_state_z_84 N (Z.quot rem 10) (sum + Z.rem rem 10)) /\
  (forall sum,
      digit_sum_state_z_84 N 0 sum ->
      sum = digit_sum_z_84 N /\ binary_safe_84 sum) /\
  (forall sum out_l,
      sum = digit_sum_z_84 N ->
      out_l = binary_output_z_84 sum ->
      problem_84_spec_z N out_l).
