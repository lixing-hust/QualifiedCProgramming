(* Given a positive integer n, return a tuple that has the number of even and odd
integer palindromes that fall within the range(1, n), inclusive. 
Example 1:

    Input: 3
    Output: (1, 2)
    Explanation:
    Integer palindrome are 1, 2, 3. one of them is even, && two of them are odd.

Example 2:

    Input: 12
    Output: (4, 6)
    Explanation:
    Integer palindrome are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11. four of them are even, && 6 of them are odd.

Note:
    1. 1 <= n <= 10^3
    2. returned vector has the number of even && odd integer palindromes respectively.
*)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Coq.Arith.Arith Coq.Numbers.DecimalString.
Import ListNotations.
Open Scope Z_scope.

(* Decimal.uint is the stdlib decimal representation produced by Nat.to_uint.
   This turns that representation into a most-significant-first digit list.
   Example: Nat.to_uint 121 is D1 (D2 (D1 Nil)), so this returns [1; 2; 1]. *)
Definition decimal_uint_digits (u : Decimal.uint) : list nat :=
  Decimal.uint_rect
    (fun _ => list nat)
    nil
    (fun _ digits => 0%nat :: digits)
    (fun _ digits => 1%nat :: digits)
    (fun _ digits => 2%nat :: digits)
    (fun _ digits => 3%nat :: digits)
    (fun _ digits => 4%nat :: digits)
    (fun _ digits => 5%nat :: digits)
    (fun _ digits => 6%nat :: digits)
    (fun _ digits => 7%nat :: digits)
    (fun _ digits => 8%nat :: digits)
    (fun _ digits => 9%nat :: digits)
    u.

(* decimal_nat_digits returns the decimal digits of n, with 0 represented as [0]. *)
Definition decimal_nat_digits (n : nat) : list nat :=
  match decimal_uint_digits (Nat.to_uint n) with
  | nil => [0%nat]
  | digits => digits
  end.

(* is_palindrome_nat recognizes decimal palindromes by comparing digits with rev. *)
Definition is_palindrome_nat (n : nat) : bool :=
  let digits := decimal_nat_digits n in
  if list_eq_dec Nat.eq_dec digits (rev digits) then true else false.

(* is_palindrome_z keeps the original positive-Z interface used by this spec. *)
Definition is_palindrome_z (x : Z) : bool :=
  if x <=? 0 then false else is_palindrome_nat (Z.to_nat x).

(* count_even_pal_upto_nat counts even palindromes in 1..k. *)
Definition count_even_pal_upto_nat (k : nat) : Z :=
  Z.of_nat
    (length
       (filter
          (fun x => andb (is_palindrome_nat x) (Nat.even x))
          (seq 1 k))).

(* count_odd_pal_upto_nat counts odd palindromes in 1..k. *)
Definition count_odd_pal_upto_nat (k : nat) : Z :=
  Z.of_nat
    (length
       (filter
          (fun x => andb (is_palindrome_nat x) (negb (Nat.even x)))
          (seq 1 k))).

(* count_even_pal_upto converts the integer bound to a finite natural range. *)
Definition count_even_pal_upto (n : Z) : Z :=
  count_even_pal_upto_nat (Z.to_nat n).

(* count_odd_pal_upto converts the integer bound to a finite natural range. *)
Definition count_odd_pal_upto (n : Z) : Z :=
  count_odd_pal_upto_nat (Z.to_nat n).

(* problem_107_pre restricts the input to the benchmark range. *)
Definition problem_107_pre (n : Z) : Prop :=
  1 <= n <= 1000.

(* problem_107_spec returns even and odd palindrome counts up to n. *)
Definition problem_107_spec (n : Z) (output : list Z) : Prop :=
  output = [count_even_pal_upto n; count_odd_pal_upto n].
