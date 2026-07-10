(* def sum_squares(lst):
This function will take a list of integers. For all entries in the list, the function shall square the integer entry if its index is a
multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not
change the entries in the list whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.

Examples:
For lst = [1,2,3] the output should be 6
For lst = [] the output should be 0
For lst = [-1,-5,2,-1,-5] the output should be -126
 *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Bool.Bool.
Import ListNotations.

(* transformed_entry applies the index-dependent square/cube rule. *)
Definition transformed_entry (n : nat) (h : Z) : Z :=
  if (Nat.modulo n 3 =? 0%nat) then (Z.mul h h)
  else if andb (Nat.modulo n 4 =? 0%nat) (negb (Nat.modulo n 3 =? 0%nat)) then Z.mul (Z.mul h h) h
  else h.

(* sum_transformed folds over the indexed entries after applying the rule. *)
Definition sum_transformed (l : list Z) (n : nat) : Z :=
  fold_left
    Z.add
    (map (fun p => transformed_entry (fst p) (snd p)) (combine (seq n (length l)) l))
    0%Z.

(* sum_squares_impl starts the transformed sum at index 0. *)
Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

(* problem_142_pre accepts any integer list. *)
Definition problem_142_pre (lst : list Z) : Prop := True.

(* problem_142_spec states that output is the transformed sum. *)
Definition problem_142_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_squares_impl lst.
