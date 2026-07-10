(* prime_fib returns n-th number that is a Fibonacci number and it's also prime.
>>> prime_fib(1)
2
>>> prime_fib(2)
3
>>> prime_fib(3)
5
>>> prime_fib(4)
13
>>> prime_fib(5)
89 *)

(* Spec(input : n. output : n) :=

​	 IsPrimeFib(r) ∧ |{y ∈ ℕ | y < r ∧ IsPrimeFib(y)}| = n - 1 *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.

(* IsPrime states primality using divisibility by natural numbers. *)
Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* fib returns the n-th Fibonacci number via Nat.iter on the adjacent pair state. *)
Definition fib (n : nat) : nat :=
  fst (Nat.iter n (fun p => (snd p, fst p + snd p)) (0, 1)).

(* IsFib says that n appears somewhere in the Fibonacci sequence. *)
Definition IsFib (n : nat) : Prop := exists i : nat, fib i = n.

(* IsPrimeFib says that a number is both prime and Fibonacci. *)
Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.


(* problem_39_pre requires a positive ordinal for the requested prime Fibonacci. *)
Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

(* problem_39_spec characterizes r as the n-th prime Fibonacci number. *)
Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    (* 1. 列表 S 的长度必须是 n-1 *)
    length S = n - 1 /\

    (* 2. 列表 S 中没有重复元素，使其能真正代表一个“集合” *)
    NoDup S /\

    (* 3. 列表 S 精确地包含了所有小于 r 的素斐波那契数 *)
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).
