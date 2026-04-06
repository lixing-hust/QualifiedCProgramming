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


Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* IsFib 命题：一个数是斐波那契数。*)

(* 关系：fib_at i v 表示 v 是第 i 个斐波那契数 *)
Inductive fib_at : nat -> nat -> Prop :=
| fib_at_0 : fib_at 0 0
| fib_at_1 : fib_at 1 1
| fib_at_S : forall i a b,
    fib_at i a ->
    fib_at (S i) b ->
    fib_at (S (S i)) (a + b).

Definition IsFib (n : nat) : Prop := exists i : nat, fib_at i n.

(* IsPrimeFib 命题：一个数既是素数又是斐波那契数 *)
Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.


(* Pre: n must be at least 1 to have a valid n-th prime-fibonacci number *)
Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

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