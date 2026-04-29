(* Given a positive integer n, return a tuple that has the number of even and odd
integer palindromes that fall within the range(1, n), inclusive. *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint reverse_digits_loop (fuel : nat) (t r : Z) : Z :=
  match fuel with
  | O => r
  | S fuel' =>
      if t >? 0
      then reverse_digits_loop fuel' (t / 10) (r * 10 + t mod 10)
      else r
  end.

Definition is_palindrome_z (x : Z) : bool :=
  if x <=? 0 then false else reverse_digits_loop 4 x 0 =? x.

Definition is_even_z (x : Z) : bool :=
  x mod 2 =? 0.

Fixpoint count_even_pal_upto_nat (k : nat) : Z :=
  match k with
  | O => 0
  | S k' =>
      let x := Z.of_nat (S k') in
      count_even_pal_upto_nat k' +
      if andb (is_palindrome_z x) (is_even_z x) then 1 else 0
  end.

Fixpoint count_odd_pal_upto_nat (k : nat) : Z :=
  match k with
  | O => 0
  | S k' =>
      let x := Z.of_nat (S k') in
      count_odd_pal_upto_nat k' +
      if andb (is_palindrome_z x) (negb (is_even_z x)) then 1 else 0
  end.

Definition count_even_pal_upto (n : Z) : Z :=
  count_even_pal_upto_nat (Z.to_nat n).

Definition count_odd_pal_upto (n : Z) : Z :=
  count_odd_pal_upto_nat (Z.to_nat n).

Definition problem_107_pre (n : Z) : Prop :=
  1 <= n <= 1000.

Definition problem_107_spec (n : Z) (output : list Z) : Prop :=
  output = [count_even_pal_upto n; count_odd_pal_upto n].
