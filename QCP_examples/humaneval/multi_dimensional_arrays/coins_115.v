Load "../spec/115".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sac.

Definition row_nat_of_z (row : list Z) : list nat :=
  map Z.to_nat row.

Definition matrix_nat_of_z (grid : list (list Z)) : list (list nat) :=
  map row_nat_of_z grid.

Definition problem_115_pre_z (grid : list (list Z)) (capacity : Z) : Prop :=
  problem_115_pre (matrix_nat_of_z grid) (Z.to_nat capacity).

Definition problem_115_spec_z
  (grid : list (list Z)) (capacity output : Z) : Prop :=
  problem_115_spec (matrix_nat_of_z grid) (Z.to_nat capacity) (Z.to_nat output).

Fixpoint int_matrix_rows_full
  (row_ptrs : list Z) (cols : Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | nil, nil => emp
  | p :: ptrs', row :: rows' =>
      IntArray.full p cols row **
      int_matrix_rows_full ptrs' cols rows'
  | _, _ => [| False |] && emp
  end.

Definition row_rect01_z (row : list Z) (cols : Z) : Prop :=
  Zlength row = cols /\
  forall i, 0 <= i < cols -> Znth i row 0 = 0 \/ Znth i row 0 = 1.

Fixpoint matrix_rect01_z (grid : list (list Z)) (cols : Z) : Prop :=
  match grid with
  | nil => True
  | row :: grid' => row_rect01_z row cols /\ matrix_rect01_z grid' cols
  end.

Fixpoint row_sum_prefix_nat (fuel : nat) (row : list Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      row_sum_prefix_nat fuel' row + Znth (Z.of_nat fuel') row 0
  end.

Definition row_sum_prefix_z (_ cols : Z) (row : list Z) : Z :=
  row_sum_prefix_nat (Z.to_nat cols) row.

Definition row_required_trips_z (row : list Z) (capacity : Z) : Z :=
  let s := row_sum_prefix_z 0 (Zlength row) row in
  if Z.eqb s 0 then 0 else (s - 1) / capacity + 1.

Fixpoint matrix_required_trips_prefix_nat
  (fuel : nat) (grid : list (list Z)) (capacity : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      matrix_required_trips_prefix_nat fuel' grid capacity +
      row_required_trips_z (Znth (Z.of_nat fuel') grid nil) capacity
  end.

Definition matrix_required_trips_prefix_z
  (rows : Z) (grid : list (list Z)) (capacity : Z) : Z :=
  matrix_required_trips_prefix_nat (Z.to_nat rows) grid capacity.
