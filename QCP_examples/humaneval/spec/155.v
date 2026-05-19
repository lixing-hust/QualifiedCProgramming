(* def even_odd_count(num):
"""Given an integer. return a tuple that has the number of even and odd digits respectively.

Example:
even_odd_count(-12) ==> (1, 1)
even_odd_count(123) ==> (1, 2)
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.ZArith.ZArith Coq.Arith.Arith.
Open Scope Z_scope.


Fixpoint count_digits_acc (l : list Z) (acc : nat * nat) : nat * nat :=
  match l with
  | nil => acc
  | h :: t =>
      let '(e,o) := acc in
      if Z.even h
      then count_digits_acc t (S e, o)
      else count_digits_acc t (e, S o)
  end.

Fixpoint to_digits_fuel_nonzero (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S f' =>
      let p := Z.abs n in
      if p =? 0 then nil else (p mod 10) :: to_digits_fuel_nonzero f' (p / 10)
  end.

Definition to_digits (n : Z) : list Z :=
  if Z.abs n =? 0
  then 0 :: nil
  else to_digits_fuel_nonzero (Z.to_nat (Z.abs n) + 1)%nat n.

Definition even_odd_count_impl (num : Z) : nat * nat :=
  count_digits_acc (to_digits num) (0%nat, 0%nat).

(* 任意整数输入 *)
Definition problem_155_pre (num : Z) : Prop := True.

Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count_impl num.
