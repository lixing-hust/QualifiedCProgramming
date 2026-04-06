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


Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => n * fact k
  end.


Definition brazilian_factorial_impl (n : nat) : nat :=
  fold_right mult 1 (map fact (seq 1 n)).

(* n > 0 *)
Definition problem_139_pre (n : nat) : Prop := n > 0.

Definition problem_139_spec (n : nat) (output : nat) : Prop :=
  output = brazilian_factorial_impl n.