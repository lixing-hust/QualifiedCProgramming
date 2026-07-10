(* def circular_shift(x, shift):
"""Circular shift the digits of the integer x, shift the digits right by shift
and return the result as a string.
If shift > number of digits, return digits reversed.
>>> circular_shift(12, 1)
"21"
>>> circular_shift(12, 2)
"12"
""" *)
(* 导入所需的标准库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.


Open Scope string_scope.


(* msd_pos returns the highest non-zero decimal position, defaulting to 0. *)
Definition msd_pos (n : nat) : nat :=
  fst
    (fold_left
       (fun acc p =>
          let d := (n / Nat.pow 10 p) mod 10 in
          if Nat.eqb d 0 then acc else (p, d))
       (seq 0 (S n))
       (0, 0)).

(* to_digits returns the decimal digits of n from most to least significant. *)
Definition to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then
    [0]
  else
    map (fun p => (n / Nat.pow 10 p) mod 10) (rev (seq 0 (S (msd_pos n)))).

(* digit_to_string converts a decimal digit to a one-character string. *)
Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

(* from_digits_to_string concatenates the one-character strings for all digits. *)
Definition from_digits_to_string (l : list nat) : string :=
  String.concat "" (map digit_to_string l).

(* circular_shift_impl rotates decimal digits right, or reverses when shift is too large. *)
Definition circular_shift_impl (x : nat) (shift : nat) : string :=
  let digits := to_digits x in
  let len := length digits in
  if (x =? 0)%nat then
    "0"
  else
    if (len <? shift)%nat then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len in
      if (effective_shift =? 0)%nat then
        from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).

(* problem_65_pre imposes no input constraints. *)
Definition problem_65_pre (x : nat) (shift : nat) : Prop := True.

(* problem_65_spec states that result is the circular-shifted decimal string. *)
Definition problem_65_spec (x : nat) (shift : nat) (result : string) : Prop :=
  result = circular_shift_impl x shift.
