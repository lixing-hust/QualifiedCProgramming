(* def solve(s):
"""You are given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
solve("1234") = "4321"
solve("ab") = "AB"
solve("#a@C") = "#A@c"
""" *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* The following predicates describe letters by their ASCII codes. *)
Definition lower_alpha (c : ascii) : Prop :=
  (97 <= nat_of_ascii c <= 122)%nat.

Definition upper_alpha (c : ascii) : Prop :=
  (65 <= nat_of_ascii c <= 90)%nat.

Definition letter (c : ascii) : Prop :=
  lower_alpha c \/ upper_alpha c.

(* case_flip relates one input character to its required output character. *)
Definition case_flip (input output : ascii) : Prop :=
  (lower_alpha input /\
   output = ascii_of_nat (nat_of_ascii input - 32)) \/
  (upper_alpha input /\
   output = ascii_of_nat (nat_of_ascii input + 32)) \/
  (~ letter input /\ output = input).

(* If a letter occurs, every character is related pointwise by case_flip. *)
Definition letters_case_flipped
    (input output : list ascii) : Prop :=
  Exists letter input /\ Forall2 case_flip input output.

(* If no letter occurs, the output is the reverse of the input. *)
Definition letter_free_reversal
    (input output : list ascii) : Prop :=
  Forall (fun c => ~ letter c) input /\ output = rev input.

Definition problem_161_pre (_ : string) : Prop := True.

(* The contract relates the character lists represented by the two strings. *)
Definition problem_161_spec (s result : string) : Prop :=
  let input := list_ascii_of_string s in
  let output := list_ascii_of_string result in
  letters_case_flipped input output \/
  letter_free_reversal input output.
