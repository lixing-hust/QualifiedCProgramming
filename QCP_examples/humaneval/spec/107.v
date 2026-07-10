(* Given a positive integer n, return a tuple that has the number of even and odd
integer palindromes that fall within the range(1, n), inclusive. *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

(* decimal_digit returns the digit at decimal position p of a non-negative number. *)
Definition decimal_digit (n : Z) (p : nat) : Z :=
  (n / Z.of_nat (Nat.pow 10 p)) mod 10.

(* msd_pos returns the highest position with a non-zero digit, defaulting to 0. *)
Definition msd_pos (n : Z) : nat :=
  fst
    (fold_left
       (fun acc p =>
          let d := decimal_digit n p in
          if d =? 0 then acc else (p, d))
       (seq 0 (Z.to_nat n + 1))
       (0%nat, 0)).

(* reverse_digits reverses the decimal digits of a positive number. *)
Definition reverse_digits (x : Z) : Z :=
  fold_left
    (fun r p => r * 10 + decimal_digit x p)
    (seq 0 (S (msd_pos x)))
    0.

(* is_palindrome_z recognizes positive decimal palindromes. *)
Definition is_palindrome_z (x : Z) : bool :=
  if x <=? 0 then false else reverse_digits x =? x.

(* is_even_z is the integer parity test used for the two output counts. *)
Definition is_even_z (x : Z) : bool :=
  x mod 2 =? 0.

(* count_even_pal_upto_nat counts even palindromes in 1..k. *)
Definition count_even_pal_upto_nat (k : nat) : Z :=
  Z.of_nat
    (length
       (filter
          (fun x => andb (is_palindrome_z (Z.of_nat x)) (is_even_z (Z.of_nat x)))
          (seq 1 k))).

(* count_odd_pal_upto_nat counts odd palindromes in 1..k. *)
Definition count_odd_pal_upto_nat (k : nat) : Z :=
  Z.of_nat
    (length
       (filter
          (fun x => andb (is_palindrome_z (Z.of_nat x)) (negb (is_even_z (Z.of_nat x))))
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
