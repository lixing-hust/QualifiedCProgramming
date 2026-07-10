(* def even_odd_count(num):
"""Given an integer. return a tuple that has the number of even and odd digits respectively.

Example:
even_odd_count(-12) ==> (1, 1)
even_odd_count(123) ==> (1, 2)
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.ZArith.ZArith Coq.Arith.Arith.
Open Scope Z_scope.

(* count_digits_acc folds over digits and accumulates even and odd counts. *)
Definition count_digits_acc (l : list Z) (acc : nat * nat) : nat * nat :=
  fold_left
    (fun eo h =>
       let '(e,o) := eo in
       if Z.even h then (S e, o) else (e, S o))
    l
    acc.

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

(* to_digits enumerates all digits of the absolute value, including 0 itself. *)
Definition to_digits (n : Z) : list Z :=
  let p := Z.abs n in
  if p =? 0
  then 0 :: nil
  else map (decimal_digit p) (seq 0 (S (msd_pos p))).

(* even_odd_count_impl returns the number of even and odd decimal digits. *)
Definition even_odd_count_impl (num : Z) : nat * nat :=
  count_digits_acc (to_digits num) (0%nat, 0%nat).

(* problem_155_pre accepts any integer input. *)
Definition problem_155_pre (num : Z) : Prop := True.

(* problem_155_spec states that output is the even/odd digit count pair. *)
Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count_impl num.
