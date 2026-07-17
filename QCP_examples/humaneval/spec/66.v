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

Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* An ASCII character is uppercase exactly when its code is in ['A', 'Z']. *)
Definition uppercase_ascii (c : ascii) : Prop :=
  (65 <= nat_of_ascii c <= 90)%nat.

(* Each character is related to the amount it contributes to the result. *)
Definition uppercase_contribution (c : ascii) (n : nat) : Prop :=
  (uppercase_ascii c /\ n = nat_of_ascii c) \/
  (~ uppercase_ascii c /\ n = 0).

(* problem_66_pre imposes no input constraints. *)
Definition problem_66_pre (s : string) : Prop := True.

(* The witness records one contribution for each input character. *)
Definition problem_66_spec (s : string) (output : nat) : Prop :=
  exists contributions : list nat,
    Forall2 uppercase_contribution
      (list_ascii_of_string s) contributions /\
    output = fold_right Nat.add 0 contributions.
