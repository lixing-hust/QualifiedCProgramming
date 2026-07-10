(* def digits(n):
"""Given a positive integer n, return the product of the odd digits.
Return 0 if all digits are even.
For example:
digits(1) == 1
digits(4) == 0
digits(235) == 15
"""*)

Require Import Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

(* get_digits enumerates enough decimal positions for n; high zero digits are harmless. *)
Definition get_digits (n : nat) : list nat :=
  map (fun p => (n / Nat.pow 10 p) mod 10) (List.seq 0 n).

(* product multiplies all numbers in a list using the standard fold combinator. *)
Definition product (l : list nat) : nat :=
  fold_left Nat.mul l 1.

(* digits_impl returns the product of odd decimal digits, or 0 if none exist. *)
Definition digits_impl (n : nat) : nat :=
  let ds := filter Nat.odd (get_digits n) in
  match ds with
  | [] => 0
  | _ => product ds
  end.

(* problem_131_pre requires a positive input. *)
Definition problem_131_pre (n : nat) : Prop := n > 0.

(* problem_131_spec states that output matches the odd-digit product. *)
Definition problem_131_spec (n : nat) (output : nat) : Prop :=
  output = digits_impl n.
