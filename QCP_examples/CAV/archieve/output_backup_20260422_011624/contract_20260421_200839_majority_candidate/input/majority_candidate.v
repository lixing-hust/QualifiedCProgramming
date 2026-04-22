Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition majority_candidate_step (candidate count x : Z) : Z * Z :=
  if Z.eq_dec count 0 then (x, 1)
  else if Z.eq_dec x candidate then (candidate, count + 1)
  else (candidate, count - 1).

Fixpoint majority_candidate_acc (candidate count : Z) (l : list Z) : Z :=
  match l with
  | nil => candidate
  | x :: xs =>
      let '(candidate', count') := majority_candidate_step candidate count x in
      majority_candidate_acc candidate' count' xs
  end.

Definition majority_candidate_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => majority_candidate_acc x 1 xs
  end.
