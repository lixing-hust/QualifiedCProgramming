(* """ Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence(0)
'0'
>>> string_sequence(5)
'0 1 2 3 4 5'
""" *)

(*  *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.DecimalString.
Import ListNotations.
Open Scope string_scope.

(* string_of_nat converts a natural number to its decimal string. *)
Definition string_of_nat (n : nat) : string :=
  DecimalString.NilZero.string_of_uint (Nat.to_uint n).

(* problem_15_pre imposes no input constraints. *)
Definition problem_15_pre (n : nat) : Prop := True.

(* problem_15_spec states that output is the space-delimited sequence. *)
Definition problem_15_spec (n : nat) (output : string) : Prop :=
  output = String.concat " " (map string_of_nat (seq 0 (S n))).
