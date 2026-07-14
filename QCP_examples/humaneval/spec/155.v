(* def even_odd_count(num):
"""Given an integer. return a tuple that has the number of even and odd digits respectively.

Example:
even_odd_count(-12) ==> (1, 1)
even_odd_count(123) ==> (1, 2)
""" *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Arith.Arith Coq.Bool.Bool.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpNumber.
Import ListNotations.
Open Scope Z_scope.

(* decimal_digits follows spec/145.v: digits are stored least-significant first. *)
Definition decimal_digits (n : Z) (digits : list Z) : Prop :=
  list_within_bound 10 digits /\
  list_to_Z 10 digits = Z.abs n /\
  ((n = 0 /\ digits = [0]) \/
   (n <> 0 /\ digits <> [] /\ last digits 0 <> 0)).

(* even_odd_digit_counts relates a digit list to its even and odd digit counts. *)
Definition even_odd_digit_counts (digits : list Z) (even odd : nat) : Prop :=
  even = length (filter Z.even digits) /\
  odd = length (filter (fun d => negb (Z.even d)) digits).

(* problem_155_pre accepts any integer input. *)
Definition problem_155_pre (num : Z) : Prop := True.

(* problem_155_spec states that output is the even/odd digit count pair. *)
Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  let '(even, odd) := output in
  exists digits,
    decimal_digits num digits /\
    even_odd_digit_counts digits even odd.
