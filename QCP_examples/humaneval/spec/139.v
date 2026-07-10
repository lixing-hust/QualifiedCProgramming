(* def special_factorial(n):
"""The Brazilian factorial is defined as:
brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
where n > 0

For example:
>>> special_factorial(4)
288

The function will receive an integer as input and should return the special
factorial of this integer.
""" *)

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(* fact computes n! as the product of the finite range 1, ..., n. *)
Definition fact (n : nat) : nat :=
  fold_left Nat.mul (seq 1 n) 1.

(* brazilian_factorial_impl multiplies all factorials from 1! through n!. *)
Definition brazilian_factorial_impl (n : nat) : nat :=
  fold_right mult 1 (map fact (seq 1 n)).

(* problem_139_pre requires a positive input. *)
Definition problem_139_pre (n : nat) : Prop := n > 0.

(* problem_139_spec states that output is the Brazilian factorial of n. *)
Definition problem_139_spec (n : nat) (output : nat) : Prop :=
  output = brazilian_factorial_impl n.
