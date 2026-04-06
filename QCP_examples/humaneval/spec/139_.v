(* def special_factorial(n):
"""The Brazilian factorial is defined as:
brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
where n > 0

For example:
>>> special_factorial(4)
288

The function will receive an integer as input and should return the special
factorial of this integer.
""" *)

Require Import Coq.Lists.List Coq.Init.Nat.
Import ListNotations.

Inductive fact_rel : nat -> nat -> Prop :=
| fr_zero : fact_rel 0 1
| fr_succ : forall n f, fact_rel n f -> fact_rel (S n) (S n * f).

Inductive seq_from_one_rel : nat -> list nat -> Prop :=
| sfor_zero : seq_from_one_rel 0 nil
| sfor_step : forall n ns, seq_from_one_rel n ns -> seq_from_one_rel (S n) (S n :: ns).

(* 新增：列表映射关系，确保 facts 列表与 nums 列表一一对应 *)
Inductive map_fact_rel : list nat -> list nat -> Prop :=
| mfr_nil : map_fact_rel nil nil
| mfr_cons : forall n ns f fs, fact_rel n f -> map_fact_rel ns fs -> map_fact_rel (n :: ns) (f :: fs).

Inductive product_list_rel : list nat -> nat -> Prop :=
| plr_nil : product_list_rel nil 1
| plr_cons : forall h t p p_tail, product_list_rel t p_tail -> p = h * p_tail ->
    product_list_rel (h :: t) p.

(* n > 0 *)
Definition problem_139_pre (n : nat) : Prop := n > 0.

Definition problem_139_spec (n : nat) (output : nat) : Prop :=
  exists nums facts, 
    seq_from_one_rel n nums /\
    map_fact_rel nums facts /\
    product_list_rel facts output.

