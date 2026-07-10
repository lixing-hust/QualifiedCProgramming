(* def digitSum(s):
Task
Write a function that takes a string as input and returns the sum of the upper characters only'
ASCII codes.

Examples:
digitSum("") => 0
digitSum("abAB") => 131
digitSum("abcCd") => 67
digitSum("helloE") => 69
digitSum("woArBld") => 131
digitSum("aAaaaXa") => 153 *)

Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* is_uppercase recognizes uppercase ASCII letters. *)
Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb 65 n) && (Nat.leb n 90).

(* sum_uppercase_ascii sums ASCII codes of uppercase characters. *)
Definition sum_uppercase_ascii (s : string) : nat :=
  fold_left Nat.add (map nat_of_ascii (filter is_uppercase (list_ascii_of_string s))) 0.

(* digitSum_impl is the public implementation-level expression. *)
Definition digitSum_impl (s : string) : nat := sum_uppercase_ascii s.

(* problem_66_pre imposes no input constraints. *)
Definition problem_66_pre (s : string) : Prop := True.

(* problem_66_spec states that output is the uppercase ASCII sum. *)
Definition problem_66_spec (s : string) (output : nat) : Prop :=
  output = digitSum_impl s.
