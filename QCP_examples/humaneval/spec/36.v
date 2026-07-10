(* Return the number of times the digit 7 appears in integers less than n which are divisible by 11 or 13.
>>> fizz_buzz(50)
0
>>> fizz_buzz(78)
2
>>> fizz_buzz(79)
3 *)

(* Spec(input : int, output : int) :=
  outout = $∑_{x=0}^{input-1}$ (if DivBy11Or13(x) then Num7sIn(x) else 0) *)

Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

(* count_digit_7 counts decimal positions whose digit is 7 by enumerating all
   positions below k; positions past the most significant digit contribute 0. *)
Definition count_digit_7 (k : nat) : nat :=
  length
    (filter
       (fun p => Nat.eqb (((k / Nat.pow 10 p) mod 10)) 7)
       (List.seq 0 k)).

(* fizz_buzz_impl sums the number of 7 digits in each qualifying integer below n. *)
Definition fizz_buzz_impl (n : nat) : nat :=
  List.fold_left
    (fun acc i =>
      acc +
      (if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
         count_digit_7 i
       else
         0))
    (List.seq 0 n)
    0.


(* problem_36_pre imposes no additional input constraints. *)
Definition problem_36_pre (n : nat) : Prop := True.

(* problem_36_spec states that the output is the finite fizz_buzz sum. *)
Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  output = fizz_buzz_impl n.
