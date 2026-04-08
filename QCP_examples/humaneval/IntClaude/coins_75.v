Load "../spec/75".
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Adapt bool result to Z: r <> 0 means true *)
Definition problem_75_spec_z (a r : Z) : Prop :=
  r <> 0 <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3.

Fixpoint list_prod (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * list_prod xs
  end.

Definition mp_outer_inv (a_pre i a num : Z) : Prop :=
  a >= 2 /\
  exists l : list Z,
    Forall prime l /\
    Z.of_nat (length l) = num /\
    a_pre = list_prod l * a /\
    (forall k : Z, 2 <= k < i -> Z.rem a k <> 0 \/ a <= k).
