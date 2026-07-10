(* You are given two positive integers n and m, and your task is to compute the
average of the integers from n through m (including n and m).
Round the answer to the nearest integer and convert that to binary.
If n is greater than m, return -1.
Example:
rounded_avg(1, 5) => "11"
rounded_avg(7, 5) => "-1"
rounded_avg(10, 20) => "1111"
rounded_avg(20, 33) => "11010" *)

(* 引入所需的库 *)
Require Import ZArith.
Require Import String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import PArith. (* 用于 positive 类型 *)
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* bit_char converts a binary digit to its ASCII character. *)
Definition bit_char (b : nat) : ascii :=
  if Nat.eqb b 0 then "0"%char else "1"%char.

(* msb_pos returns the highest non-zero binary position, defaulting to 0. *)
Definition msb_pos (n : nat) : nat :=
  fst
    (fold_left
       (fun acc p =>
          let b := Nat.modulo (Nat.div n (Nat.pow 2 p)) 2 in
          if Nat.eqb b 0 then acc else (p, b))
       (seq 0 (S n))
       (0%nat, 0%nat)).

(* nat_to_binary converts a natural number to its binary string. *)
Definition nat_to_binary (n : nat) : string :=
  match n with
  | O => "0"
  | _ =>
      string_of_list_ascii
        (map (fun p => bit_char (Nat.modulo (Nat.div n (Nat.pow 2 p)) 2)) (rev (seq 0 (S (msb_pos n)))))
  end.

(* to_binary converts integers to the benchmark binary string convention. *)
Definition to_binary (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => nat_to_binary (Pos.to_nat p)
  | Zneg _ => "-1"
  end.

(* rounded_avg_impl returns -1 for an empty interval, otherwise the rounded average in binary. *)
Definition rounded_avg_impl (n m : Z) : string :=
  if Z.gtb n m then
    "-1"
  else
    to_binary ((n + m) / 2).

(* problem_103_pre requires positive endpoints. *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

(* problem_103_spec states that output is the benchmark rounded-average string. *)
Definition problem_103_spec (n m : Z) (output : string) : Prop :=
  output = rounded_avg_impl n m.
