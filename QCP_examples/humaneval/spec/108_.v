(* Write a function count_nums which takes an array of integers and returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, and 3.
>>> count_nums([]) == 0
>>> count_nums([-1, 11, -11]) == 1
>>> count_nums([1, 1, 2]) == 3 *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.Init.Nat.
Import ListNotations.
Open Scope Z_scope.

Inductive to_digits_Z_rel : Z -> list nat -> Prop :=
| tdz_zero : to_digits_Z_rel 0%Z nil
| tdz_step : forall n d ds, 0 < n -> d = Z.to_nat (n mod 10) ->
   to_digits_Z_rel (n / 10) ds ->
   to_digits_Z_rel n (d :: ds).

Inductive digits_of_Z_rel : Z -> list nat -> Prop :=
| doz_zero : digits_of_Z_rel 0%Z nil
| doz_pos : forall n ds, 0 < n -> to_digits_Z_rel n ds -> digits_of_Z_rel n ds.

Inductive sum_digits_rel_from_list : list nat -> Z -> Prop :=
| sdrfl_nil : sum_digits_rel_from_list nil 0%Z
| sdrfl_cons : forall d ds s, sum_digits_rel_from_list ds s ->
   sum_digits_rel_from_list (d :: ds) (Z.of_nat d + s).

(* most-significant digit: since digits lists are produced with least-significant
   digit at head, the msd is the last element of the list *)
Inductive msd_of_digits : list nat -> nat -> Prop :=
| mod_single : forall d, msd_of_digits (d :: nil) d
| mod_cons : forall d ds m, msd_of_digits ds m -> msd_of_digits (d :: ds) m.

Inductive sum_digits_rel : Z -> Z -> Prop :=
| sdr_zero : sum_digits_rel 0%Z 0%Z
| sdr_pos : forall n s ds, 0 < n -> digits_of_Z_rel n ds -> sum_digits_rel_from_list ds s ->
   sum_digits_rel n s
| sdr_neg : forall n s p ds s_pos m,
    n < 0 ->
    p = Z.to_nat (- n) ->
    digits_of_Z_rel (Z.of_nat p) ds ->
    sum_digits_rel_from_list ds s_pos ->
    msd_of_digits ds m ->
    s = s_pos - 2 * (Z.of_nat m) ->
    sum_digits_rel n s.

Inductive count_nums_rel : list Z -> nat -> Prop :=
| cnr_nil : count_nums_rel nil 0%nat
| cnr_hit : forall h t n s, sum_digits_rel h s -> s > 0%Z -> count_nums_rel t n ->
   count_nums_rel (h :: t) (S n)
| cnr_miss : forall h t n s, sum_digits_rel h s -> (s <= 0%Z) -> count_nums_rel t n ->
   count_nums_rel (h :: t) n.

(* 输入列表可为任意整数列表 *)
Definition problem_108_pre (l : list Z) : Prop := True.

Definition problem_108_spec (l : list Z) (output : nat) : Prop :=
  count_nums_rel l output.

