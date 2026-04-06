(* The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fib4(0) -> 0
fib4(1) -> 0
fib4(2) -> 2
fib4(3) -> 0
fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
Please write a function to efficiently compute the n-th element of the fib4 number sequence. Do not use recursion.
>>> fib4(5)
4
>>> fib4(6)
8
>>> fib4(7)
14 *)

(* 
  Spec(input : int, output : int) :=

​	∃ Fib : list int,
​		Fib[0] = 0 /\ Fib[1] = 0 /\ Fib[2] = 2 /\ Fib[3] = 0 /\
​		∀i ∈ N, i >3 → Fib[i] = Fib[i-1] + Fib[i-2] + Fib[i-3] + Fib[i-4] /\
​		output = Fib[input] *)


Require Import Coq.Arith.Arith.

(* 使用 Fixpoint 表示 fib4 序列 *)
Fixpoint fib4 (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n1 =>
    match n1 with
    | 0 => 0
    | S n2 =>
      match n2 with
      | 0 => 2
      | S n3 =>
        match n3 with
        | 0 => 0
        | S n4 => fib4 n1 + fib4 n2 + fib4 n3 + fib4 n4
        end
      end
    end
  end.


Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  output = fib4 input.