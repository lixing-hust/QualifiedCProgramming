(* def add(lst):
"""Given a non-empty list of integers lst. add the even elements that are at odd indices..


Examples:
add([4, 2, 6, 7]) ==> 2
""" *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

(* sum_even_at_odd_indices sums even values paired with odd zero-based indices. *)
Definition sum_even_at_odd_indices (l : list Z) (n : nat) : Z :=
  fold_left
    Z.add
    (map
       (fun p =>
          let idx := fst p in
          let h := snd p in
          if andb (Nat.odd idx) (Z.even h) then h else 0)
       (combine (seq n (length l)) l))
    0.

(* add_impl starts the indexed sum at index 0. *)
Definition add_impl (lst : list Z) : Z := sum_even_at_odd_indices lst 0.

(* problem_85_pre requires a non-empty list. *)
Definition problem_85_pre (lst : list Z) : Prop := lst <> []%list.

(* problem_85_spec states that output is the selected-index sum. *)
Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  output = add_impl lst.
