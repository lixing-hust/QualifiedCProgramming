Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_129.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function minPath -----*)

Definition minPath_safety_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 k_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 k_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 k_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "y" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH20 : (0 <= x)) (PreH21 : (x < n_pre)) (PreH22 : (0 <= y)) (PreH23 : (y < n_pre)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (0 <= one_x)) (PreH17 : (one_x < n_pre)) (PreH18 : (0 <= one_y)) (PreH19 : (one_y < n_pre)) (PreH20 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH21 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH22 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH23 : (0 <= x)) (PreH24 : (x < n_pre)) (PreH25 : (0 <= y)) (PreH26 : (y < n_pre)) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> j)
  **  ((( &( "x" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition minPath_safety_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) <> 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition minPath_safety_wit_8 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y )) (PreH19 : (0 <= x)) (PreH20 : (x < n_pre)) (PreH21 : (0 <= y)) (PreH22 : (y < n_pre)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition minPath_safety_wit_9 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * n_pre )) ”
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * n_pre )) ”
).

Definition minPath_safety_wit_9_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre * n_pre ) <= INT_MAX) ”
.

Definition minPath_safety_wit_9_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  ((( &( "min" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((INT_MIN) <= (n_pre * n_pre )) ”
.

Definition minPath_safety_wit_10 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_11 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 < x)) (PreH8 : (x < n_pre)) (PreH9 : (0 <= y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
|--
  “ ((x - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x - 1 )) ”
.

Definition minPath_safety_wit_12 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 < x)) (PreH8 : (x < n_pre)) (PreH9 : (0 <= y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_13 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((x - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x - 1 )) ”
.

Definition minPath_safety_wit_14 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_15 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition minPath_safety_wit_16 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition minPath_safety_wit_17 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_18 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_19 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x >= (n_pre - 1 ))) (PreH2 : (x <= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ False ”
.

Definition minPath_safety_wit_20 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : ((x + 1 ) < n_pre)) (PreH9 : (0 <= y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
|--
  “ ((x + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition minPath_safety_wit_21 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : ((x + 1 ) < n_pre)) (PreH9 : (0 <= y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_22 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((x + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition minPath_safety_wit_23 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_24 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_25 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_26 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : (x < n_pre)) (PreH9 : (0 < y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
|--
  “ ((y - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y - 1 )) ”
.

Definition minPath_safety_wit_27 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : (x < n_pre)) (PreH9 : (0 < y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_28 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((y - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y - 1 )) ”
.

Definition minPath_safety_wit_29 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_30 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y <= 0)) (PreH2 : (x >= (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition minPath_safety_wit_31 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition minPath_safety_wit_32 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition minPath_safety_wit_33 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_34 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_35 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y <= 0)) (PreH2 : (x >= (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_36 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y >= (n_pre - 1 ))) (PreH2 : (y <= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ False ”
.

Definition minPath_safety_wit_37 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y >= (n_pre - 1 ))) (PreH2 : (y <= 0)) (PreH3 : (x >= (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ False ”
.

Definition minPath_safety_wit_38 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : (x < n_pre)) (PreH9 : (0 <= y)) (PreH10 : ((y + 1 ) < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition minPath_safety_wit_39 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : (x < n_pre)) (PreH9 : (0 <= y)) (PreH10 : ((y + 1 ) < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_40 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition minPath_safety_wit_41 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_42 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : (checked_neighbor_min_129 rows n_pre x y 4 min )) (PreH10 : (min_neighbor_state_129 rows n_pre x y min )) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_43 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : (t < k_pre)) (PreH2 : (0 <= t)) (PreH3 : (t <= k_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : (min_neighbor_state_129 rows n_pre x y min )) (PreH13 : (output_prefix_129 k_pre min t output_l )) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntArray.undef_seg data t k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((t <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition minPath_safety_wit_44 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : (t < k_pre)) (PreH2 : (0 <= t)) (PreH3 : (t <= k_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : (min_neighbor_state_129 rows n_pre x y min )) (PreH13 : (output_prefix_129 k_pre min t output_l )) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntArray.undef_seg data t k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition minPath_safety_wit_45 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : (t < k_pre)) (PreH2 : (0 <= t)) (PreH3 : (t <= k_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : (min_neighbor_state_129 rows n_pre x y min )) (PreH13 : (output_prefix_129 k_pre min t output_l )) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntArray.undef_seg data t k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minPath_safety_wit_46 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) = 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l )) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntArray.undef_seg data t k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minPath_safety_wit_47 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) = 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l )) ,
  (IntArray.seg data 0 (t + 1 ) (app (output_l) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition minPath_safety_wit_48 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) <> 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l )) ,
  (IntArray.seg data 0 (t + 1 ) (app (output_l) ((cons (min) ((@nil Z))))) )
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "min" ) )) # Int  |-> min)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition minPath_entail_wit_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  (IntArray.undef_full retval_2 k_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ ((n_pre * n_pre ) < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre 0 0 0 0 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full retval_2 k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  (IntArray.undef_full retval_2 k_pre )
|--
  “ (find_one_scan_state_129 rows n_pre 0 0 0 0 ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full retval_2 k_pre )
).

Definition minPath_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  (IntArray.undef_full retval_2 k_pre )
|--
  “ (find_one_scan_state_129 rows n_pre 0 0 0 0 ) ”
.

Definition minPath_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  (IntArray.undef_full retval_2 k_pre )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : ((n_pre * n_pre ) < INT_MAX)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (problem_129_pre_z rows k_pre )) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH11 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH12 : (0 <= one_x)) (PreH13 : (one_x < n_pre)) (PreH14 : (0 <= one_y)) (PreH15 : (one_y < n_pre)) (PreH16 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  (IntArray.undef_full retval_2 k_pre )
|--
  (IntArray.undef_full retval_2 k_pre )
.

Definition minPath_entail_wit_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre i 0 x y ) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
  **  (IntArray.undef_full data k_pre )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
  **  (IntArray.undef_full data k_pre )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre) ”
.

Definition minPath_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
  **  (IntArray.undef_full data k_pre )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_2_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
  **  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
  **  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition minPath_entail_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH20 : (0 <= x)) (PreH21 : (x < n_pre)) (PreH22 : (0 <= y)) (PreH23 : (y < n_pre)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr_2 rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (row_ptr: Z) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre i 0 x y ) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition minPath_entail_wit_4_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr_2 rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
|--
  EX (row_ptr: Z) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre i (j + 1 ) i j ) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ (find_one_scan_state_129 rows n_pre i (j + 1 ) i j ) ”
  &&  (IntArray.undef_full data k_pre )
).

Definition minPath_entail_wit_4_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ (find_one_scan_state_129 rows n_pre i (j + 1 ) i j ) ”
.

Definition minPath_entail_wit_4_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
.

Definition minPath_entail_wit_4_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) <> 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr_2 rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
|--
  EX (row_ptr: Z) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre i (j + 1 ) x y ) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) <> 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ (find_one_scan_state_129 rows n_pre i (j + 1 ) x y ) ”
  &&  (IntArray.undef_full data k_pre )
).

Definition minPath_entail_wit_4_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) <> 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ (find_one_scan_state_129 rows n_pre i (j + 1 ) x y ) ”
.

Definition minPath_entail_wit_4_2_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (rows) ((@nil Z))) 0) <> 1)) (PreH2 : (j < n_pre)) (PreH3 : (0 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre < INT_MAX)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : (0 <= one_x)) (PreH18 : (one_x < n_pre)) (PreH19 : (0 <= one_y)) (PreH20 : (one_y < n_pre)) (PreH21 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH22 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH23 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH24 : (0 <= x)) (PreH25 : (x < n_pre)) (PreH26 : (0 <= y)) (PreH27 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
.

Definition minPath_entail_wit_5 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (0 <= one_x)) (PreH17 : (one_x < n_pre)) (PreH18 : (0 <= one_y)) (PreH19 : (one_y < n_pre)) (PreH20 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH21 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH22 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH23 : (0 <= x)) (PreH24 : (x < n_pre)) (PreH25 : (0 <= y)) (PreH26 : (y < n_pre)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (0 <= one_x)) (PreH17 : (one_x < n_pre)) (PreH18 : (0 <= one_y)) (PreH19 : (one_y < n_pre)) (PreH20 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH21 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH22 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH23 : (0 <= x)) (PreH24 : (x < n_pre)) (PreH25 : (0 <= y)) (PreH26 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (0 <= one_x)) (PreH17 : (one_x < n_pre)) (PreH18 : (0 <= one_y)) (PreH19 : (one_y < n_pre)) (PreH20 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH21 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH22 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH23 : (0 <= x)) (PreH24 : (x < n_pre)) (PreH25 : (0 <= y)) (PreH26 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y ) ”
.

Definition minPath_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (0 <= one_x)) (PreH17 : (one_x < n_pre)) (PreH18 : (0 <= one_y)) (PreH19 : (one_y < n_pre)) (PreH20 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH21 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH22 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH23 : (0 <= x)) (PreH24 : (x < n_pre)) (PreH25 : (0 <= y)) (PreH26 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_5_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (0 <= one_x)) (PreH17 : (one_x < n_pre)) (PreH18 : (0 <= one_y)) (PreH19 : (one_y < n_pre)) (PreH20 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH21 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH22 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH23 : (0 <= x)) (PreH24 : (x < n_pre)) (PreH25 : (0 <= y)) (PreH26 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_6 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y )) (PreH19 : (0 <= x)) (PreH20 : (x < n_pre)) (PreH21 : (0 <= y)) (PreH22 : (y < n_pre)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ ((n_pre * n_pre ) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y )) (PreH19 : (0 <= x)) (PreH20 : (x < n_pre)) (PreH21 : (0 <= y)) (PreH22 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((n_pre * n_pre ) < INT_MAX) ”
  &&  (IntArray.undef_full data k_pre )
).

Definition minPath_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y )) (PreH19 : (0 <= x)) (PreH20 : (x < n_pre)) (PreH21 : (0 <= y)) (PreH22 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_6_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y )) (PreH19 : (0 <= x)) (PreH20 : (x < n_pre)) (PreH21 : (0 <= y)) (PreH22 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ ((n_pre * n_pre ) < INT_MAX) ”
.

Definition minPath_entail_wit_6_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (0 <= one_x)) (PreH14 : (one_x < n_pre)) (PreH15 : (0 <= one_y)) (PreH16 : (one_y < n_pre)) (PreH17 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH18 : (find_one_scan_state_129 rows n_pre (i + 1 ) 0 x y )) (PreH19 : (0 <= x)) (PreH20 : (x < n_pre)) (PreH21 : (0 <= y)) (PreH22 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
.

Definition minPath_entail_wit_7 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (find_one_scan_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full data k_pre )
).

Definition minPath_entail_wit_7_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ”
.

Definition minPath_entail_wit_7_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ (find_one_scan_state_129 rows n_pre n_pre 0 x y ) ”
.

Definition minPath_entail_wit_7_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_7_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : ((n_pre * n_pre ) < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (0 <= one_x)) (PreH16 : (one_x < n_pre)) (PreH17 : (0 <= one_y)) (PreH18 : (one_y < n_pre)) (PreH19 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH20 : (find_one_scan_state_129 rows n_pre i 0 x y )) (PreH21 : (0 <= x)) (PreH22 : (x < n_pre)) (PreH23 : (0 <= y)) (PreH24 : (y < n_pre)) ,
  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
.

Definition minPath_entail_wit_8 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 0 (n_pre * n_pre ) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (checked_neighbor_min_129 rows n_pre x y 0 (n_pre * n_pre ) ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (1 <= (n_pre * n_pre )) ”
  &&  (IntArray.undef_full data k_pre )
).

Definition minPath_entail_wit_8_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (checked_neighbor_min_129 rows n_pre x y 0 (n_pre * n_pre ) ) ”
.

Definition minPath_entail_wit_8_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  (IntArray.undef_full data k_pre )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_8_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (1 <= (n_pre * n_pre )) ”
.

Definition minPath_entail_wit_8_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH16 : (find_one_scan_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (find_one_state_129 rows n_pre n_pre 0 x y )) ,
  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
.

Definition minPath_entail_wit_9 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 < x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 0 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 < x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 0 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_10_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_10_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
.

Definition minPath_entail_wit_10_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_10_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_10_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0)) ” 
  &&  “ ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 1 (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (1 <= (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0)) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_10_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 1 (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) ) ”
.

Definition minPath_entail_wit_10_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_10_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0)) ”
.

Definition minPath_entail_wit_10_2_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_11_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x < (n_pre - 1 ))) (PreH2 : (x <= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ ((x + 1 ) < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x < (n_pre - 1 ))) (PreH2 : (x <= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ ((x + 1 ) < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_11_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x < (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ ((x + 1 ) < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (x < (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ ((x + 1 ) < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_12_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_12_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
.

Definition minPath_entail_wit_12_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_12_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_12_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0)) ” 
  &&  “ ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 2 (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (1 <= (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0)) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_12_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 2 (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) ) ”
.

Definition minPath_entail_wit_12_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_12_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0)) ”
.

Definition minPath_entail_wit_12_2_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_13_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y > 0)) (PreH2 : (x >= (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 < y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y > 0)) (PreH2 : (x >= (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 < y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_13_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 < y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 < y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_14_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_14_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
.

Definition minPath_entail_wit_14_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_14_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_14_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0)) ” 
  &&  “ ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 3 (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (1 <= (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0)) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_14_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 3 (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) ) ”
.

Definition minPath_entail_wit_14_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_14_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0)) ”
.

Definition minPath_entail_wit_14_2_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_15_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y < (n_pre - 1 ))) (PreH2 : (y <= 0)) (PreH3 : (x >= (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y < (n_pre - 1 ))) (PreH2 : (y <= 0)) (PreH3 : (x >= (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH17 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_15_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y < (n_pre - 1 ))) (PreH2 : (y <= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y < (n_pre - 1 ))) (PreH2 : (y <= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (1 <= min)) (PreH10 : (min <= (n_pre * n_pre ))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : (problem_129_pre_z rows k_pre )) (PreH13 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH14 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH15 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH16 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_15_3 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y < (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y < (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
).

Definition minPath_entail_wit_16_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 4 min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 4 min ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_16_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 4 min ) ”
.

Definition minPath_entail_wit_16_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_16_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) >= min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_16_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0)) ” 
  &&  “ ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 4 (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 4 (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (1 <= (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0)) ”
  &&  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
).

Definition minPath_entail_wit_16_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (checked_neighbor_min_129 rows n_pre x y 4 (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) ) ”
.

Definition minPath_entail_wit_16_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ”
.

Definition minPath_entail_wit_16_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0)) ”
.

Definition minPath_entail_wit_16_2_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < n_pre)) -> ((1 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_entail_wit_17_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 4 min ) ” 
  &&  “ (min_neighbor_state_129 rows n_pre x y min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (min_neighbor_state_129 rows n_pre x y min ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 4 min ) ”
  &&  (IntArray.undef_full data k_pre )
).

Definition minPath_entail_wit_17_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (min_neighbor_state_129 rows n_pre x y min ) ”
.

Definition minPath_entail_wit_17_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (checked_neighbor_min_129 rows n_pre x y 4 min ) ”
.

Definition minPath_entail_wit_17_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (y >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (1 <= min)) (PreH9 : (min <= (n_pre * n_pre ))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : (problem_129_pre_z rows k_pre )) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH13 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH14 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH15 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
.

Definition minPath_entail_wit_17_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 4 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 4 min ) ” 
  &&  “ (min_neighbor_state_129 rows n_pre x y min ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 4 min )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (min_neighbor_state_129 rows n_pre x y min ) ”
  &&  (IntArray.undef_full data k_pre )
).

Definition minPath_entail_wit_17_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 4 min )) ,
  (IntArray.undef_full data k_pre )
|--
  “ (min_neighbor_state_129 rows n_pre x y min ) ”
.

Definition minPath_entail_wit_17_2_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : ((Zlength (rows)) = n_pre)) (PreH10 : (problem_129_pre_z rows k_pre )) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH13 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH14 : (checked_neighbor_min_129 rows n_pre x y 4 min )) ,
  (IntArray.undef_full data k_pre )
|--
  (IntArray.undef_full data k_pre )
.

Definition minPath_entail_wit_18 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : (checked_neighbor_min_129 rows n_pre x y 4 min )) (PreH10 : (min_neighbor_state_129 rows n_pre x y min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ (min_neighbor_state_129 rows n_pre x y min ) ” 
  &&  “ (output_prefix_129 k_pre min 0 output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 0 output_l )
  **  (IntArray.undef_seg data 0 k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : (checked_neighbor_min_129 rows n_pre x y 4 min )) (PreH10 : (min_neighbor_state_129 rows n_pre x y min )) ,
  TT && emp 
|--
  “ (output_prefix_129 k_pre min 0 (@nil Z) ) ”
  &&  emp
).

Definition minPath_entail_wit_18_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (out: Z) (data: Z) (min: Z) (y: Z) (x: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= min)) (PreH8 : (min <= (n_pre * n_pre ))) (PreH9 : (checked_neighbor_min_129 rows n_pre x y 4 min )) (PreH10 : (min_neighbor_state_129 rows n_pre x y min )) ,
  TT && emp 
|--
  “ (output_prefix_129 k_pre min 0 (@nil Z) ) ”
.

Definition minPath_entail_wit_19_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) = 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l_2 )) ,
  (IntArray.seg data 0 (t + 1 ) (app (output_l_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ (min_neighbor_state_129 rows n_pre x y min ) ” 
  &&  “ (output_prefix_129 k_pre min (t + 1 ) output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 (t + 1 ) output_l )
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) = 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l_2 )) ,
  TT && emp 
|--
  “ (output_prefix_129 k_pre min (t + 1 ) (app (output_l_2) ((cons (1) ((@nil Z))))) ) ”
  &&  emp
).

Definition minPath_entail_wit_19_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) = 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l_2 )) ,
  TT && emp 
|--
  “ (output_prefix_129 k_pre min (t + 1 ) (app (output_l_2) ((cons (1) ((@nil Z))))) ) ”
.

Definition minPath_entail_wit_19_2 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) <> 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l_2 )) ,
  (IntArray.seg data 0 (t + 1 ) (app (output_l_2) ((cons (min) ((@nil Z))))) )
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ (min_neighbor_state_129 rows n_pre x y min ) ” 
  &&  “ (output_prefix_129 k_pre min (t + 1 ) output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 (t + 1 ) output_l )
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) <> 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l_2 )) ,
  TT && emp 
|--
  “ (output_prefix_129 k_pre min (t + 1 ) (app (output_l_2) ((cons (min) ((@nil Z))))) ) ”
  &&  emp
).

Definition minPath_entail_wit_19_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) <> 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l_2 )) ,
  TT && emp 
|--
  “ (output_prefix_129 k_pre min (t + 1 ) (app (output_l_2) ((cons (min) ((@nil Z))))) ) ”
.

Definition minPath_return_wit_1 := 
(
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data_2: Z) (out: Z) (t: Z) (PreH1 : (t >= k_pre)) (PreH2 : (0 <= t)) (PreH3 : (t <= k_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data_2 <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : (min_neighbor_state_129 rows n_pre x y min )) (PreH13 : (output_prefix_129 k_pre min t output_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data_2 0 t output_l_2 )
  **  (IntArray.undef_seg data_2 t k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  EX (data: Z)  (output_l: (@list Z))  (minv: Z) ,
  “ (out <> 0) ” 
  &&  “ (1 <= minv) ” 
  &&  “ (minv <= (n_pre * n_pre )) ” 
  &&  “ (problem_129_spec_z rows k_pre output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
  **  (IntArray.full data k_pre output_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (output_l_2: (@list Z)) (x: Z) (y: Z) (min: Z) (data_2: Z) (out: Z) (t: Z) (PreH1 : (t >= k_pre)) (PreH2 : (0 <= t)) (PreH3 : (t <= k_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (data_2 <> 0)) (PreH10 : (1 <= min)) (PreH11 : (min <= (n_pre * n_pre ))) (PreH12 : (min_neighbor_state_129 rows n_pre x y min )) (PreH13 : (output_prefix_129 k_pre min t output_l_2 )) ,
  (IntArray.seg data_2 0 t output_l_2 )
|--
  EX (output_l: (@list Z))  (minv: Z) ,
  “ (out <> 0) ” 
  &&  “ (1 <= minv) ” 
  &&  “ (minv <= (n_pre * n_pre )) ” 
  &&  “ (problem_129_spec_z rows k_pre output_l ) ”
  &&  (IntArray.full data_2 k_pre output_l )
).

Definition minPath_partial_solve_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : ((n_pre * n_pre ) < INT_MAX)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (problem_129_pre_z rows k_pre )) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH10 : (0 <= one_x)) (PreH11 : (one_x < n_pre)) (PreH12 : (0 <= one_y)) (PreH13 : (one_y < n_pre)) (PreH14 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ ((n_pre * n_pre ) < INT_MAX) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ”
  &&  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_partial_solve_wit_2_pure := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : ((n_pre * n_pre ) < INT_MAX)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (k_pre >= 0) ” 
  &&  “ (k_pre < INT_MAX) ”
.

Definition minPath_partial_solve_wit_2_aux := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : ((n_pre * n_pre ) < INT_MAX)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (problem_129_pre_z rows k_pre )) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH11 : (0 <= one_x)) (PreH12 : (one_x < n_pre)) (PreH13 : (0 <= one_y)) (PreH14 : (one_y < n_pre)) (PreH15 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ (k_pre >= 0) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ ((n_pre * n_pre ) < INT_MAX) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_partial_solve_wit_2 := minPath_partial_solve_wit_2_pure -> minPath_partial_solve_wit_2_aux.

Definition minPath_partial_solve_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (one_y: Z) (one_x: Z) (rows: (@list (@list Z))) (row_ptr: Z) (x: Z) (y: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < n_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : ((Zlength (rows)) = n_pre)) (PreH13 : (problem_129_pre_z rows k_pre )) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH16 : (0 <= one_x)) (PreH17 : (one_x < n_pre)) (PreH18 : (0 <= one_y)) (PreH19 : (one_y < n_pre)) (PreH20 : ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1)) (PreH21 : (find_one_scan_state_129 rows n_pre i j x y )) (PreH22 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre)) (PreH23 : (0 <= x)) (PreH24 : (x < n_pre)) (PreH25 : (0 <= y)) (PreH26 : (y < n_pre)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ (0 <= one_x) ” 
  &&  “ (one_x < n_pre) ” 
  &&  “ (0 <= one_y) ” 
  &&  “ (one_y < n_pre) ” 
  &&  “ ((Znth one_y (Znth one_x rows __default__List_Z) 0) = 1) ” 
  &&  “ (find_one_scan_state_129 rows n_pre i j x y ) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ”
  &&  (((row_ptr + (j * sizeof(INT) ) )) # Int  |-> (Znth j (Znth (i) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 < x)) (PreH8 : (x < n_pre)) (PreH9 : (0 <= y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 < x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 0 min ) ”
  &&  (((row_ptr + (y * sizeof(INT) ) )) # Int  |-> (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr y 0 (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 < x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 0 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0) < min) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 < x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 0 min ) ”
  &&  (((row_ptr + (y * sizeof(INT) ) )) # Int  |-> (Znth y (Znth ((x - 1 )) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr y 0 (Zlength ((Znth ((x - 1 )) (rows) ((@nil Z))))) (Znth ((x - 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x - 1 ) row_ptr rows )
  **  (((grid_pre + ((x - 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : ((x + 1 ) < n_pre)) (PreH9 : (0 <= y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ ((x + 1 ) < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
  &&  (((row_ptr + (y * sizeof(INT) ) )) # Int  |-> (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr y 0 (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : ((x + 1 ) < n_pre)) (PreH10 : (0 <= y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 1 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0) < min) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ ((x + 1 ) < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 1 min ) ”
  &&  (((row_ptr + (y * sizeof(INT) ) )) # Int  |-> (Znth y (Znth ((x + 1 )) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr y 0 (Zlength ((Znth ((x + 1 )) (rows) ((@nil Z))))) (Znth ((x + 1 )) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre (x + 1 ) row_ptr rows )
  **  (((grid_pre + ((x + 1 ) * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_8 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : (x < n_pre)) (PreH9 : (0 < y)) (PreH10 : (y < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 < y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
  &&  (((row_ptr + ((y - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr (y - 1 ) 0 (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_9 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 < y)) (PreH11 : (y < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 2 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 < y) ” 
  &&  “ (y < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 2 min ) ”
  &&  (((row_ptr + ((y - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (y - 1 ) (Znth (x) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr (y - 1 ) 0 (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_10 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre < INT_MAX)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= x)) (PreH8 : (x < n_pre)) (PreH9 : (0 <= y)) (PreH10 : ((y + 1 ) < n_pre)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : (problem_129_pre_z rows k_pre )) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH17 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH18 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH19 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  (((row_ptr + ((y + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr (y + 1 ) 0 (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_11 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (data: Z) (x: Z) (y: Z) (min: Z)  __default__List_Z (PreH1 : ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= x)) (PreH9 : (x < n_pre)) (PreH10 : (0 <= y)) (PreH11 : ((y + 1 ) < n_pre)) (PreH12 : (1 <= min)) (PreH13 : (min <= (n_pre * n_pre ))) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : (problem_129_pre_z rows k_pre )) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre ))))) (PreH18 : ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre)) (PreH19 : (find_one_state_129 rows n_pre n_pre 0 x y )) (PreH20 : (checked_neighbor_min_129 rows n_pre x y 3 min )) ,
  (IntArray.full row_ptr (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0) < min) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((y + 1 ) < n_pre) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (problem_129_pre_z rows k_pre ) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = n_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < n_pre)) -> ((1 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= (n_pre * n_pre )))) ” 
  &&  “ ((Zlength ((Znth (x) (rows) ((@nil Z))))) = n_pre) ” 
  &&  “ (find_one_state_129 rows n_pre n_pre 0 x y ) ” 
  &&  “ (checked_neighbor_min_129 rows n_pre x y 3 min ) ”
  &&  (((row_ptr + ((y + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (y + 1 ) (Znth (x) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr (y + 1 ) 0 (Zlength ((Znth (x) (rows) ((@nil Z))))) (Znth (x) (rows) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.undef_full data k_pre )
  **  (IntPtrArray2.missing_i grid_pre n_pre x row_ptr rows )
  **  (((grid_pre + (x * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition minPath_partial_solve_wit_12 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) = 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntArray.undef_seg data t k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((t % ( 2 ) ) = 0) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ (min_neighbor_state_129 rows n_pre x y min ) ” 
  &&  “ (output_prefix_129 k_pre min t output_l ) ”
  &&  (((data + (t * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Definition minPath_partial_solve_wit_13 := 
forall (k_pre: Z) (n_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (output_l: (@list Z)) (x: Z) (y: Z) (min: Z) (data: Z) (out: Z) (t: Z) (PreH1 : ((t % ( 2 ) ) <> 0)) (PreH2 : (t < k_pre)) (PreH3 : (0 <= t)) (PreH4 : (t <= k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre < INT_MAX)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (1 <= min)) (PreH12 : (min <= (n_pre * n_pre ))) (PreH13 : (min_neighbor_state_129 rows n_pre x y min )) (PreH14 : (output_prefix_129 k_pre min t output_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntArray.undef_seg data t k_pre )
  **  (IntPtrArray2.full grid_pre n_pre rows )
|--
  “ ((t % ( 2 ) ) <> 0) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= min) ” 
  &&  “ (min <= (n_pre * n_pre )) ” 
  &&  “ (min_neighbor_state_129 rows n_pre x y min ) ” 
  &&  “ (output_prefix_129 k_pre min t output_l ) ”
  &&  (((data + (t * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (t + 1 ) k_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.seg data 0 t output_l )
  **  (IntPtrArray2.full grid_pre n_pre rows )
.

Module Type VC_Correct.

Include int_ptr_array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_minPath_safety_wit_1 : minPath_safety_wit_1.
Axiom proof_of_minPath_safety_wit_2 : minPath_safety_wit_2.
Axiom proof_of_minPath_safety_wit_3 : minPath_safety_wit_3.
Axiom proof_of_minPath_safety_wit_4 : minPath_safety_wit_4.
Axiom proof_of_minPath_safety_wit_5 : minPath_safety_wit_5.
Axiom proof_of_minPath_safety_wit_6 : minPath_safety_wit_6.
Axiom proof_of_minPath_safety_wit_7 : minPath_safety_wit_7.
Axiom proof_of_minPath_safety_wit_8 : minPath_safety_wit_8.
Axiom proof_of_minPath_safety_wit_9 : minPath_safety_wit_9.
Axiom proof_of_minPath_safety_wit_10 : minPath_safety_wit_10.
Axiom proof_of_minPath_safety_wit_11 : minPath_safety_wit_11.
Axiom proof_of_minPath_safety_wit_12 : minPath_safety_wit_12.
Axiom proof_of_minPath_safety_wit_13 : minPath_safety_wit_13.
Axiom proof_of_minPath_safety_wit_14 : minPath_safety_wit_14.
Axiom proof_of_minPath_safety_wit_15 : minPath_safety_wit_15.
Axiom proof_of_minPath_safety_wit_16 : minPath_safety_wit_16.
Axiom proof_of_minPath_safety_wit_17 : minPath_safety_wit_17.
Axiom proof_of_minPath_safety_wit_18 : minPath_safety_wit_18.
Axiom proof_of_minPath_safety_wit_19 : minPath_safety_wit_19.
Axiom proof_of_minPath_safety_wit_20 : minPath_safety_wit_20.
Axiom proof_of_minPath_safety_wit_21 : minPath_safety_wit_21.
Axiom proof_of_minPath_safety_wit_22 : minPath_safety_wit_22.
Axiom proof_of_minPath_safety_wit_23 : minPath_safety_wit_23.
Axiom proof_of_minPath_safety_wit_24 : minPath_safety_wit_24.
Axiom proof_of_minPath_safety_wit_25 : minPath_safety_wit_25.
Axiom proof_of_minPath_safety_wit_26 : minPath_safety_wit_26.
Axiom proof_of_minPath_safety_wit_27 : minPath_safety_wit_27.
Axiom proof_of_minPath_safety_wit_28 : minPath_safety_wit_28.
Axiom proof_of_minPath_safety_wit_29 : minPath_safety_wit_29.
Axiom proof_of_minPath_safety_wit_30 : minPath_safety_wit_30.
Axiom proof_of_minPath_safety_wit_31 : minPath_safety_wit_31.
Axiom proof_of_minPath_safety_wit_32 : minPath_safety_wit_32.
Axiom proof_of_minPath_safety_wit_33 : minPath_safety_wit_33.
Axiom proof_of_minPath_safety_wit_34 : minPath_safety_wit_34.
Axiom proof_of_minPath_safety_wit_35 : minPath_safety_wit_35.
Axiom proof_of_minPath_safety_wit_36 : minPath_safety_wit_36.
Axiom proof_of_minPath_safety_wit_37 : minPath_safety_wit_37.
Axiom proof_of_minPath_safety_wit_38 : minPath_safety_wit_38.
Axiom proof_of_minPath_safety_wit_39 : minPath_safety_wit_39.
Axiom proof_of_minPath_safety_wit_40 : minPath_safety_wit_40.
Axiom proof_of_minPath_safety_wit_41 : minPath_safety_wit_41.
Axiom proof_of_minPath_safety_wit_42 : minPath_safety_wit_42.
Axiom proof_of_minPath_safety_wit_43 : minPath_safety_wit_43.
Axiom proof_of_minPath_safety_wit_44 : minPath_safety_wit_44.
Axiom proof_of_minPath_safety_wit_45 : minPath_safety_wit_45.
Axiom proof_of_minPath_safety_wit_46 : minPath_safety_wit_46.
Axiom proof_of_minPath_safety_wit_47 : minPath_safety_wit_47.
Axiom proof_of_minPath_safety_wit_48 : minPath_safety_wit_48.
Axiom proof_of_minPath_entail_wit_1 : minPath_entail_wit_1.
Axiom proof_of_minPath_entail_wit_2 : minPath_entail_wit_2.
Axiom proof_of_minPath_entail_wit_3 : minPath_entail_wit_3.
Axiom proof_of_minPath_entail_wit_4_1 : minPath_entail_wit_4_1.
Axiom proof_of_minPath_entail_wit_4_2 : minPath_entail_wit_4_2.
Axiom proof_of_minPath_entail_wit_5 : minPath_entail_wit_5.
Axiom proof_of_minPath_entail_wit_6 : minPath_entail_wit_6.
Axiom proof_of_minPath_entail_wit_7 : minPath_entail_wit_7.
Axiom proof_of_minPath_entail_wit_8 : minPath_entail_wit_8.
Axiom proof_of_minPath_entail_wit_9 : minPath_entail_wit_9.
Axiom proof_of_minPath_entail_wit_10_1 : minPath_entail_wit_10_1.
Axiom proof_of_minPath_entail_wit_10_2 : minPath_entail_wit_10_2.
Axiom proof_of_minPath_entail_wit_11_1 : minPath_entail_wit_11_1.
Axiom proof_of_minPath_entail_wit_11_2 : minPath_entail_wit_11_2.
Axiom proof_of_minPath_entail_wit_12_1 : minPath_entail_wit_12_1.
Axiom proof_of_minPath_entail_wit_12_2 : minPath_entail_wit_12_2.
Axiom proof_of_minPath_entail_wit_13_1 : minPath_entail_wit_13_1.
Axiom proof_of_minPath_entail_wit_13_2 : minPath_entail_wit_13_2.
Axiom proof_of_minPath_entail_wit_14_1 : minPath_entail_wit_14_1.
Axiom proof_of_minPath_entail_wit_14_2 : minPath_entail_wit_14_2.
Axiom proof_of_minPath_entail_wit_15_1 : minPath_entail_wit_15_1.
Axiom proof_of_minPath_entail_wit_15_2 : minPath_entail_wit_15_2.
Axiom proof_of_minPath_entail_wit_15_3 : minPath_entail_wit_15_3.
Axiom proof_of_minPath_entail_wit_16_1 : minPath_entail_wit_16_1.
Axiom proof_of_minPath_entail_wit_16_2 : minPath_entail_wit_16_2.
Axiom proof_of_minPath_entail_wit_17_1 : minPath_entail_wit_17_1.
Axiom proof_of_minPath_entail_wit_17_2 : minPath_entail_wit_17_2.
Axiom proof_of_minPath_entail_wit_18 : minPath_entail_wit_18.
Axiom proof_of_minPath_entail_wit_19_1 : minPath_entail_wit_19_1.
Axiom proof_of_minPath_entail_wit_19_2 : minPath_entail_wit_19_2.
Axiom proof_of_minPath_return_wit_1 : minPath_return_wit_1.
Axiom proof_of_minPath_partial_solve_wit_1 : minPath_partial_solve_wit_1.
Axiom proof_of_minPath_partial_solve_wit_2_pure : minPath_partial_solve_wit_2_pure.
Axiom proof_of_minPath_partial_solve_wit_2 : minPath_partial_solve_wit_2.
Axiom proof_of_minPath_partial_solve_wit_3 : minPath_partial_solve_wit_3.
Axiom proof_of_minPath_partial_solve_wit_4 : minPath_partial_solve_wit_4.
Axiom proof_of_minPath_partial_solve_wit_5 : minPath_partial_solve_wit_5.
Axiom proof_of_minPath_partial_solve_wit_6 : minPath_partial_solve_wit_6.
Axiom proof_of_minPath_partial_solve_wit_7 : minPath_partial_solve_wit_7.
Axiom proof_of_minPath_partial_solve_wit_8 : minPath_partial_solve_wit_8.
Axiom proof_of_minPath_partial_solve_wit_9 : minPath_partial_solve_wit_9.
Axiom proof_of_minPath_partial_solve_wit_10 : minPath_partial_solve_wit_10.
Axiom proof_of_minPath_partial_solve_wit_11 : minPath_partial_solve_wit_11.
Axiom proof_of_minPath_partial_solve_wit_12 : minPath_partial_solve_wit_12.
Axiom proof_of_minPath_partial_solve_wit_13 : minPath_partial_solve_wit_13.

End VC_Correct.
