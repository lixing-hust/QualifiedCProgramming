Load "../spec/79".

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

Definition ascii_of_z_79 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_79 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_79 c) (string_of_list_z_79 rest)
  end.

Definition problem_79_pre_z (decimal : Z) : Prop :=
  problem_79_pre (Z.to_nat decimal).

Definition problem_79_spec_z (decimal : Z) (output : list Z) : Prop :=
  problem_79_spec (Z.to_nat decimal) (string_of_list_z_79 output).

Fixpoint binary_bits_fuel_79 (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if Z.leb n 0 then []
      else (n mod 2) :: binary_bits_fuel_79 fuel' (n / 2)
  end.

Definition binary_bits_pos_z_79 (n : Z) : list Z :=
  binary_bits_fuel_79 (Z.to_nat n) n.

Definition binary_bits_z_79 (n : Z) : list Z :=
  if Z.eqb n 0 then [0] else binary_bits_pos_z_79 n.

Definition bit_code_z_79 (b : Z) : Z := 48 + b.

Definition binary_payload_z_79 (n : Z) : list Z :=
  map bit_code_z_79 (rev (binary_bits_z_79 n)).

Definition decorated_binary_output_z_79 (n : Z) : list Z :=
  [100; 98] ++ binary_payload_z_79 n ++ [100; 98].

Definition binary_length_z_79 (n : Z) : Z :=
  Zlength (binary_payload_z_79 n).

Definition binary_count_state_z_79 (orig x bits : Z) : Prop :=
  0 <= x /\
  0 <= bits /\
  bits + 1 <= INT_MAX /\
  INT_MIN <= bits + 1 /\
  bits + Zlength (binary_bits_pos_z_79 x) =
    Zlength (binary_bits_pos_z_79 orig).

Definition binary_divisor_state_z_79
    (orig i divisor : Z) : Prop :=
  0 < orig /\
  1 <= i <= binary_length_z_79 orig /\
  1 <= divisor <= INT_MAX.

Definition binary_write_state_z_79
    (orig rem divisor pos : Z) (out_l : list Z) : Prop :=
  0 < orig /\
  0 <= rem <= orig /\
  0 <= divisor <= INT_MAX /\
  2 <= pos <= binary_length_z_79 orig + 2 /\
  binary_length_z_79 orig + 5 < INT_MAX /\
  pos < binary_length_z_79 orig + 5 /\
  pos + 1 <= INT_MAX /\
  INT_MIN <= pos + 1 /\
  pos + 2 <= INT_MAX /\
  INT_MIN <= pos + 2 /\
  Zlength out_l = pos /\
  (forall i, 0 <= i < Zlength out_l -> 0 <= Znth i out_l 0 <= 127).

Definition binary_safe_79 (decimal : Z) : Prop :=
  binary_count_state_z_79 decimal decimal 0 /\
  (forall x bits,
      binary_count_state_z_79 decimal x bits ->
      0 < x ->
      binary_count_state_z_79 decimal (x / 2) (bits + 1)) /\
  (forall bits,
      0 < decimal ->
      binary_count_state_z_79 decimal 0 bits ->
      bits = binary_length_z_79 decimal) /\
  (forall bits,
      0 < decimal ->
      bits = binary_length_z_79 decimal ->
      1 <= bits) /\
  binary_divisor_state_z_79 decimal 1 1 /\
  (forall i divisor,
      binary_divisor_state_z_79 decimal i divisor ->
      i < binary_length_z_79 decimal ->
      divisor * 2 <= INT_MAX /\
      binary_divisor_state_z_79 decimal (i + 1) (divisor * 2)) /\
  (forall divisor,
      0 < decimal ->
      binary_divisor_state_z_79
        decimal (binary_length_z_79 decimal) divisor ->
      binary_write_state_z_79 decimal decimal divisor 2 [100; 98]) /\
  (forall rem divisor pos out_l,
      binary_write_state_z_79 decimal rem divisor pos out_l ->
      0 < divisor ->
      divisor <= rem ->
      pos < binary_length_z_79 decimal + 5 /\
      binary_write_state_z_79
        decimal (rem - divisor) (divisor / 2) (pos + 1)
        (out_l ++ [49])) /\
  (forall rem divisor pos out_l,
      binary_write_state_z_79 decimal rem divisor pos out_l ->
      0 < divisor ->
      rem < divisor ->
      pos < binary_length_z_79 decimal + 5 /\
      binary_write_state_z_79
        decimal rem (divisor / 2) (pos + 1)
        (out_l ++ [48])) /\
  (forall rem pos out_l,
      binary_write_state_z_79 decimal rem 0 pos out_l ->
      out_l = [100; 98] ++ binary_payload_z_79 decimal /\
      pos = binary_length_z_79 decimal + 2) /\
  (forall out_l,
      out_l = [100; 98] ++ binary_payload_z_79 decimal ->
      out_l ++ [100; 98] = decorated_binary_output_z_79 decimal) /\
  (forall out_l,
      0 < decimal ->
      out_l = decorated_binary_output_z_79 decimal ->
      Zlength out_l = binary_length_z_79 decimal + 4) /\
  decorated_binary_output_z_79 0 = [100; 98; 48; 100; 98] /\
  (forall out_l,
      out_l = decorated_binary_output_z_79 decimal ->
      problem_79_spec_z decimal out_l).
