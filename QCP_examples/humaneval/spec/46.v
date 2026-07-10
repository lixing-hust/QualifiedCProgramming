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

(* fib4 computes the sequence by iterating the four-value sliding window. *)
Definition fib4 (n : nat) : nat :=
  let '(a, b, c, d) :=
    Nat.iter n (fun '(a, b, c, d) => (b, c, d, a + b + c + d)) (0, 0, 2, 0)
  in a.

(* problem_46_pre imposes no input constraints. *)
Definition problem_46_pre (input : nat) : Prop := True.

(* problem_46_spec states that output is the requested Fib4 value. *)
Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  output = fib4 input.
