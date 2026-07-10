(* def fib(n: int):
Return n-th Fibonacci number.
>>> fib(10)
55
>>> fib(1)
1
>>> fib(8)
21
*)
(* 引入Coq标准库，用于自然数（nat）的定义 *)
Require Import Coq.Init.Nat.

(* fib computes the n-th Fibonacci number by iterating the adjacent pair state. *)
Definition fib (n : nat) : nat :=
  fst (Nat.iter n (fun p => (snd p, fst p + snd p)) (0, 1)).

(*
  fib_spec 是对 fib 函数的程序规约。

  参数：
  - n: nat    (代表程序的输入)
  - res: nat  (代表程序的输出)

*)
(* problem_55_pre imposes no input constraints. *)
Definition problem_55_pre (n : nat) : Prop := True.

(* problem_55_spec states that res is the n-th Fibonacci number. *)
Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  res = fib n.
