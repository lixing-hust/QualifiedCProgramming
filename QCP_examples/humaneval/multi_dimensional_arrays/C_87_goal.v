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
Require Import coins_87.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function get_row -----*)

Definition get_row_safety_wit_1 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre <= 100)) (PreH3 : ((Zlength (matrix)) = rows_pre)) (PreH4 : ((Zlength (sizes)) = rows_pre)) (PreH5 : (row_sizes_match_87 matrix sizes )) (PreH6 : (problem_87_pre_z matrix x_pre )) (PreH7 : (0 <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH8 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_2 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre <= 100)) (PreH3 : ((Zlength (matrix)) = rows_pre)) (PreH4 : ((Zlength (sizes)) = rows_pre)) (PreH5 : (row_sizes_match_87 matrix sizes )) (PreH6 : (problem_87_pre_z matrix x_pre )) (PreH7 : (0 <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH8 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH10 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_3 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
|--
  “ ((total + (Znth i sizes 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + (Znth i sizes 0) )) ”
) \/
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
|--
  “ ((total + (Znth i sizes 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + (Znth i sizes 0) )) ”
).

Definition get_row_safety_wit_3_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
|--
  “ ((total + (Znth i sizes 0) ) <= INT_MAX) ”
.

Definition get_row_safety_wit_3_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
|--
  “ ((INT_MIN) <= (total + (Znth i sizes 0) )) ”
.

Definition get_row_safety_wit_4 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> (total + (Znth i sizes 0) ))
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_row_safety_wit_5 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : ((Zlength (matrix)) = rows_pre)) (PreH8 : ((Zlength (sizes)) = rows_pre)) (PreH9 : (row_sizes_match_87 matrix sizes )) (PreH10 : (problem_87_pre_z matrix x_pre )) (PreH11 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH12 : (0 <= total)) (PreH13 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH14 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_6 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : ((Zlength (matrix)) = rows_pre)) (PreH8 : ((Zlength (sizes)) = rows_pre)) (PreH9 : (row_sizes_match_87 matrix sizes )) (PreH10 : (problem_87_pre_z matrix x_pre )) (PreH11 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH12 : (0 <= total)) (PreH13 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH14 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (((total * 2 ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total * 2 ) + 2 )) ”
.

Definition get_row_safety_wit_7 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : ((Zlength (matrix)) = rows_pre)) (PreH8 : ((Zlength (sizes)) = rows_pre)) (PreH9 : (row_sizes_match_87 matrix sizes )) (PreH10 : (problem_87_pre_z matrix x_pre )) (PreH11 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH12 : (0 <= total)) (PreH13 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH14 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ ((total * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total * 2 )) ”
.

Definition get_row_safety_wit_8 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : ((Zlength (matrix)) = rows_pre)) (PreH8 : ((Zlength (sizes)) = rows_pre)) (PreH9 : (row_sizes_match_87 matrix sizes )) (PreH10 : (problem_87_pre_z matrix x_pre )) (PreH11 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH12 : (0 <= total)) (PreH13 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH14 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_row_safety_wit_9 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : ((Zlength (matrix)) = rows_pre)) (PreH8 : ((Zlength (sizes)) = rows_pre)) (PreH9 : (row_sizes_match_87 matrix sizes )) (PreH10 : (problem_87_pre_z matrix x_pre )) (PreH11 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH12 : (0 <= total)) (PreH13 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH14 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_row_safety_wit_10 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 ((total * 2 ) + 2 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_11 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((( &( "out_len" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 ((total * 2 ) + 2 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_12 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 ((total * 2 ) + 2 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_13 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l )) (PreH15 : (out_len = (Zlength (output_l)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (((Znth i sizes 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i sizes 0) - 1 )) ”
) \/
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l )) (PreH15 : (out_len = (Zlength (output_l)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (((Znth i sizes 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i sizes 0) - 1 )) ”
).

Definition get_row_safety_wit_13_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l )) (PreH15 : (out_len = (Zlength (output_l)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (((Znth i sizes 0) - 1 ) <= INT_MAX) ”
.

Definition get_row_safety_wit_13_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l )) (PreH15 : (out_len = (Zlength (output_l)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ ((INT_MIN) <= ((Znth i sizes 0) - 1 )) ”
.

Definition get_row_safety_wit_14 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l )) (PreH15 : (out_len = (Zlength (output_l)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_15 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((-1) <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_len = (output_size * 2 ))) (PreH10 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH11 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH12 : ((Zlength (matrix)) = rows_pre)) (PreH13 : ((Zlength (sizes)) = rows_pre)) (PreH14 : (row_sizes_match_87 matrix sizes )) (PreH15 : (problem_87_pre_z matrix x_pre )) (PreH16 : (scan_state_87 matrix x_pre i j output_l )) (PreH17 : (out_len = (Zlength (output_l)))) (PreH18 : (0 <= output_size)) (PreH19 : (output_size <= (total + 1 ))) (PreH20 : (0 <= out_len)) (PreH21 : (out_len <= ((total * 2 ) + 2 ))) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH24 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_16 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 (out_len + 1 ) (app (output_l) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data (out_len + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ ((out_len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + 1 )) ”
.

Definition get_row_safety_wit_17 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 (out_len + 1 ) (app (output_l) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data (out_len + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_18 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ ((out_len + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + 2 )) ”
.

Definition get_row_safety_wit_19 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_row_safety_wit_20 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + 2 ))
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition get_row_safety_wit_21 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + 2 ))
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_22 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + 2 ))
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition get_row_safety_wit_23 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + 2 ))
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_24 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l )) (PreH19 : (out_len = (Zlength (output_l)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition get_row_safety_wit_25 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l )) (PreH19 : (out_len = (Zlength (output_l)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_26 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (prefix_state_87 matrix x_pre (i + 1 ) output_l )) (PreH15 : (out_len = (Zlength (output_l)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH21 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_row_entail_wit_1 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre <= 100)) (PreH3 : ((Zlength (matrix)) = rows_pre)) (PreH4 : ((Zlength (sizes)) = rows_pre)) (PreH5 : (row_sizes_match_87 matrix sizes )) (PreH6 : (problem_87_pre_z matrix x_pre )) (PreH7 : (0 <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH8 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (0 = (total_cells_prefix_87 (matrix) (0))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre <= 100)) (PreH3 : ((Zlength (matrix)) = rows_pre)) (PreH4 : ((Zlength (sizes)) = rows_pre)) (PreH5 : (row_sizes_match_87 matrix sizes )) (PreH6 : (problem_87_pre_z matrix x_pre )) (PreH7 : (0 <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH8 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ” 
  &&  “ (0 = (total_cells_prefix_87 (matrix) (0))) ”
  &&  emp
).

Definition get_row_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre <= 100)) (PreH3 : ((Zlength (matrix)) = rows_pre)) (PreH4 : ((Zlength (sizes)) = rows_pre)) (PreH5 : (row_sizes_match_87 matrix sizes )) (PreH6 : (problem_87_pre_z matrix x_pre )) (PreH7 : (0 <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH8 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
.

Definition get_row_entail_wit_1_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre <= 100)) (PreH3 : ((Zlength (matrix)) = rows_pre)) (PreH4 : ((Zlength (sizes)) = rows_pre)) (PreH5 : (row_sizes_match_87 matrix sizes )) (PreH6 : (problem_87_pre_z matrix x_pre )) (PreH7 : (0 <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH8 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (0 = (total_cells_prefix_87 (matrix) (0))) ”
.

Definition get_row_entail_wit_2 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ ((total + (Znth i sizes 0) ) = (total_cells_prefix_87 (matrix) ((i + 1 )))) ” 
  &&  “ (0 <= (total + (Znth i sizes 0) )) ” 
  &&  “ ((total + (Znth i sizes 0) ) <= (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((total + (Znth i sizes 0) ) <= (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (0 <= (total + (Znth i sizes 0) )) ” 
  &&  “ ((total + (Znth i sizes 0) ) = (total_cells_prefix_87 (matrix) ((i + 1 )))) ”
  &&  emp
).

Definition get_row_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((total + (Znth i sizes 0) ) <= (total_cells_prefix_87 (matrix) (rows_pre))) ”
.

Definition get_row_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (0 <= (total + (Znth i sizes 0) )) ”
.

Definition get_row_entail_wit_2_split_goal_3 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((total + (Znth i sizes 0) ) = (total_cells_prefix_87 (matrix) ((i + 1 )))) ”
.

Definition get_row_entail_wit_3 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.undef_full retval_2 ((total * 2 ) + 2 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 = (0 * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (prefix_state_87 matrix x_pre 0 output_l ) ” 
  &&  “ (0 = (Zlength (output_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (total + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((total * 2 ) + 2 )) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (prefix_state_87 matrix x_pre 0 (@nil Z) ) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ”
  &&  emp
).

Definition get_row_entail_wit_3_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
.

Definition get_row_entail_wit_3_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition get_row_entail_wit_3_split_goal_3 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (prefix_state_87 matrix x_pre 0 (@nil Z) ) ”
.

Definition get_row_entail_wit_3_split_goal_4 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z) (retval_2: Z)  __default__List_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : ((Zlength (matrix)) = rows_pre)) (PreH9 : ((Zlength (sizes)) = rows_pre)) (PreH10 : (row_sizes_match_87 matrix sizes )) (PreH11 : (problem_87_pre_z matrix x_pre )) (PreH12 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH13 : (0 <= total)) (PreH14 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH15 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ”
.

Definition get_row_entail_wit_4 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_len = (output_size * 2 ))) (PreH9 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= (total + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total * 2 ) + 2 ))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l_2 )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  EX (row_ptr: Z)  (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_len = (output_size * 2 ))) (PreH9 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= (total + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total * 2 ) + 2 ))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i matrix __default__List_Z))) (Znth i matrix __default__List_Z) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l_2 ) ”
  &&  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
).

Definition get_row_entail_wit_4_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_len = (output_size * 2 ))) (PreH9 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= (total + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total * 2 ) + 2 ))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i matrix __default__List_Z))) (Znth i matrix __default__List_Z) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
.

Definition get_row_entail_wit_4_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_len = (output_size * 2 ))) (PreH9 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= (total + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total * 2 ) + 2 ))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i matrix __default__List_Z))) (Znth i matrix __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ”
.

Definition get_row_entail_wit_4_split_goal_3 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_len = (output_size * 2 ))) (PreH9 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= (total + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total * 2 ) + 2 ))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i matrix __default__List_Z))) (Znth i matrix __default__List_Z) )
|--
  “ (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l_2 ) ”
.

Definition get_row_entail_wit_4_split_goal_spatial := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_len = (output_size * 2 ))) (PreH9 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= (total + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total * 2 ) + 2 ))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i matrix __default__List_Z))) (Znth i matrix __default__List_Z) )
|--
  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
.

Definition get_row_entail_wit_5 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr_2: Z) (output_l_2: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l_2 )) (PreH15 : (out_len = (Zlength (output_l_2)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_sizes_pre rows_pre sizes )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.seg data 0 out_len output_l_2 )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  EX (row_ptr: Z)  (output_l: (@list Z)) ,
  “ ((-1) <= ((Znth i sizes 0) - 1 )) ” 
  &&  “ (((Znth i sizes 0) - 1 ) < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l_2 )) (PreH15 : (out_len = (Zlength (output_l_2)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ” 
  &&  “ ((-1) <= ((Znth i sizes 0) - 1 )) ”
  &&  emp
).

Definition get_row_entail_wit_5_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l_2 )) (PreH15 : (out_len = (Zlength (output_l_2)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
.

Definition get_row_entail_wit_5_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l_2 )) (PreH15 : (out_len = (Zlength (output_l_2)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH22 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((-1) <= ((Znth i sizes 0) - 1 )) ”
.

Definition get_row_entail_wit_6 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr_2: Z) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH26 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l_2 )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  EX (row_ptr: Z)  (output_l: (@list Z)) ,
  “ (0 <= j) ” 
  &&  “ (j < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((out_len + 1 ) < ((total * 2 ) + 2 )) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ (scan_state_87 matrix x_pre i j output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH26 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ” 
  &&  “ ((out_len + 1 ) < ((total * 2 ) + 2 )) ” 
  &&  “ ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre) ”
  &&  emp
).

Definition get_row_entail_wit_6_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH26 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
.

Definition get_row_entail_wit_6_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH26 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((out_len + 1 ) < ((total * 2 ) + 2 )) ”
.

Definition get_row_entail_wit_6_split_goal_3 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH26 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre) ”
.

Definition get_row_entail_wit_7_1 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr_2: Z) (output_l_2: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH24 : (out_len = (Zlength (output_l_2)))) (PreH25 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH26 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l_2) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  EX (row_ptr: Z)  (output_l: (@list Z)) ,
  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((out_len + 2 ) = ((output_size + 1 ) * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (scan_state_87 matrix x_pre i (j - 1 ) output_l ) ” 
  &&  “ ((out_len + 2 ) = (Zlength (output_l))) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (total + 1 )) ” 
  &&  “ (0 <= (out_len + 2 )) ” 
  &&  “ ((out_len + 2 ) <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 (out_len + 2 ) output_l )
  **  (IntArray.undef_seg data (out_len + 2 ) ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH24 : (out_len = (Zlength (output_l_2)))) (PreH25 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH26 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 ((out_len + 1 ) + 1 ) (app ((app (output_l_2) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
|--
  EX (output_l: (@list Z)) ,
  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((out_len + 2 ) = ((output_size + 1 ) * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (scan_state_87 matrix x_pre i (j - 1 ) output_l ) ” 
  &&  “ ((out_len + 2 ) = (Zlength (output_l))) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (total + 1 )) ” 
  &&  “ (0 <= (out_len + 2 )) ” 
  &&  “ ((out_len + 2 ) <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (IntArray.seg data 0 (out_len + 2 ) output_l )
).

Definition get_row_entail_wit_7_2 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr_2: Z) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l_2 )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  EX (row_ptr: Z)  (output_l: (@list Z)) ,
  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (scan_state_87 matrix x_pre i (j - 1 ) output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (scan_state_87 matrix x_pre i (j - 1 ) output_l_2 ) ”
  &&  emp
).

Definition get_row_entail_wit_7_2_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth j (Znth (i) (matrix) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : ((-1) <= j)) (PreH4 : (j < (Znth i sizes 0))) (PreH5 : (0 <= i)) (PreH6 : (i < rows_pre)) (PreH7 : (0 <= rows_pre)) (PreH8 : (rows_pre <= 100)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_len = (output_size * 2 ))) (PreH12 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH14 : ((Zlength (matrix)) = rows_pre)) (PreH15 : ((Zlength (sizes)) = rows_pre)) (PreH16 : (row_sizes_match_87 matrix sizes )) (PreH17 : (problem_87_pre_z matrix x_pre )) (PreH18 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH19 : (out_len = (Zlength (output_l_2)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= (total + 1 ))) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= ((total * 2 ) + 2 ))) (PreH24 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (scan_state_87 matrix x_pre i (j - 1 ) output_l_2 ) ”
.

Definition get_row_entail_wit_8 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 0)) (PreH2 : ((-1) <= j)) (PreH3 : (j < (Znth i sizes 0))) (PreH4 : (0 <= i)) (PreH5 : (i < rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((Zlength (matrix)) = rows_pre)) (PreH14 : ((Zlength (sizes)) = rows_pre)) (PreH15 : (row_sizes_match_87 matrix sizes )) (PreH16 : (problem_87_pre_z matrix x_pre )) (PreH17 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH18 : (out_len = (Zlength (output_l_2)))) (PreH19 : (0 <= output_size)) (PreH20 : (output_size <= (total + 1 ))) (PreH21 : (0 <= out_len)) (PreH22 : (out_len <= ((total * 2 ) + 2 ))) (PreH23 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH24 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH25 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l_2 )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (prefix_state_87 matrix x_pre (i + 1 ) output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 0)) (PreH2 : ((-1) <= j)) (PreH3 : (j < (Znth i sizes 0))) (PreH4 : (0 <= i)) (PreH5 : (i < rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((Zlength (matrix)) = rows_pre)) (PreH14 : ((Zlength (sizes)) = rows_pre)) (PreH15 : (row_sizes_match_87 matrix sizes )) (PreH16 : (problem_87_pre_z matrix x_pre )) (PreH17 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH18 : (out_len = (Zlength (output_l_2)))) (PreH19 : (0 <= output_size)) (PreH20 : (output_size <= (total + 1 ))) (PreH21 : (0 <= out_len)) (PreH22 : (out_len <= ((total * 2 ) + 2 ))) (PreH23 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH24 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH25 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ” 
  &&  “ (prefix_state_87 matrix x_pre (i + 1 ) output_l_2 ) ”
  &&  (IntPtrArray2.full lst_pre rows_pre matrix )
).

Definition get_row_entail_wit_8_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 0)) (PreH2 : ((-1) <= j)) (PreH3 : (j < (Znth i sizes 0))) (PreH4 : (0 <= i)) (PreH5 : (i < rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((Zlength (matrix)) = rows_pre)) (PreH14 : ((Zlength (sizes)) = rows_pre)) (PreH15 : (row_sizes_match_87 matrix sizes )) (PreH16 : (problem_87_pre_z matrix x_pre )) (PreH17 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH18 : (out_len = (Zlength (output_l_2)))) (PreH19 : (0 <= output_size)) (PreH20 : (output_size <= (total + 1 ))) (PreH21 : (0 <= out_len)) (PreH22 : (out_len <= ((total * 2 ) + 2 ))) (PreH23 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH24 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH25 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
.

Definition get_row_entail_wit_8_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 0)) (PreH2 : ((-1) <= j)) (PreH3 : (j < (Znth i sizes 0))) (PreH4 : (0 <= i)) (PreH5 : (i < rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((Zlength (matrix)) = rows_pre)) (PreH14 : ((Zlength (sizes)) = rows_pre)) (PreH15 : (row_sizes_match_87 matrix sizes )) (PreH16 : (problem_87_pre_z matrix x_pre )) (PreH17 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH18 : (out_len = (Zlength (output_l_2)))) (PreH19 : (0 <= output_size)) (PreH20 : (output_size <= (total + 1 ))) (PreH21 : (0 <= out_len)) (PreH22 : (out_len <= ((total * 2 ) + 2 ))) (PreH23 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH24 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH25 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
|--
  “ (prefix_state_87 matrix x_pre (i + 1 ) output_l_2 ) ”
.

Definition get_row_entail_wit_8_split_goal_spatial := 
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l_2: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 0)) (PreH2 : ((-1) <= j)) (PreH3 : (j < (Znth i sizes 0))) (PreH4 : (0 <= i)) (PreH5 : (i < rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((Zlength (matrix)) = rows_pre)) (PreH14 : ((Zlength (sizes)) = rows_pre)) (PreH15 : (row_sizes_match_87 matrix sizes )) (PreH16 : (problem_87_pre_z matrix x_pre )) (PreH17 : (scan_state_87 matrix x_pre i j output_l_2 )) (PreH18 : (out_len = (Zlength (output_l_2)))) (PreH19 : (0 <= output_size)) (PreH20 : (output_size <= (total + 1 ))) (PreH21 : (0 <= out_len)) (PreH22 : (out_len <= ((total * 2 ) + 2 ))) (PreH23 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH24 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH25 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
|--
  (IntPtrArray2.full lst_pre rows_pre matrix )
.

Definition get_row_entail_wit_9 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (prefix_state_87 matrix x_pre (i + 1 ) output_l_2 )) (PreH15 : (out_len = (Zlength (output_l_2)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH21 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l_2 )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (prefix_state_87 matrix x_pre (i + 1 ) output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (prefix_state_87 matrix x_pre (i + 1 ) output_l_2 )) (PreH15 : (out_len = (Zlength (output_l_2)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH21 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  emp
).

Definition get_row_entail_wit_9_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (prefix_state_87 matrix x_pre (i + 1 ) output_l_2 )) (PreH15 : (out_len = (Zlength (output_l_2)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < rows_pre)) -> ((0 <= (Znth r_3 sizes 0)) /\ ((Znth r_3 sizes 0) <= 100)))) (PreH21 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < rows_pre)) /\ (0 <= c_2)) /\ (c_2 < (Znth r_4 sizes 0))) -> ((INT_MIN <= (Znth c_2 (Znth r_4 matrix __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
.

Definition get_row_return_wit_1 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total_2: Z) (output_size_2: Z) (out_len: Z) (data_2: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data_2 <> 0)) (PreH8 : (out_len = (output_size_2 * 2 ))) (PreH9 : (total_2 = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total_2 * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size_2)) (PreH18 : (output_size_2 <= (total_2 + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total_2 * 2 ) + 2 ))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data_2 0 out_len output_l_2 )
  **  (IntArray.undef_seg data_2 out_len ((total_2 * 2 ) + 2 ) )
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z)  (total: Z) ,
  “ (out <> 0) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ ((output_size * 2 ) = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (problem_87_spec_z matrix x_pre output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 (output_size * 2 ) output_l )
  **  (IntArray.undef_seg data (output_size * 2 ) ((total * 2 ) + 2 ) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (output_l_2: (@list Z)) (total_2: Z) (output_size_2: Z) (out_len: Z) (data_2: Z) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data_2 <> 0)) (PreH8 : (out_len = (output_size_2 * 2 ))) (PreH9 : (total_2 = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH10 : (((total_2 * 2 ) + 2 ) < INT_MAX)) (PreH11 : ((Zlength (matrix)) = rows_pre)) (PreH12 : ((Zlength (sizes)) = rows_pre)) (PreH13 : (row_sizes_match_87 matrix sizes )) (PreH14 : (problem_87_pre_z matrix x_pre )) (PreH15 : (prefix_state_87 matrix x_pre i output_l_2 )) (PreH16 : (out_len = (Zlength (output_l_2)))) (PreH17 : (0 <= output_size_2)) (PreH18 : (output_size_2 <= (total_2 + 1 ))) (PreH19 : (0 <= out_len)) (PreH20 : (out_len <= ((total_2 * 2 ) + 2 ))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data_2 0 out_len output_l_2 )
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ ((output_size_2 * 2 ) = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size_2) ” 
  &&  “ (output_size_2 <= ((total_cells_prefix_87 (matrix) (rows_pre)) + 1 )) ” 
  &&  “ (problem_87_spec_z matrix x_pre output_l ) ”
  &&  (IntArray.seg data_2 0 (output_size_2 * 2 ) output_l )
).

Definition get_row_partial_solve_wit_1 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (i < rows_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (i))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (((row_sizes_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i sizes 0))
  **  (IntArray.missing_i row_sizes_pre i 0 rows_pre sizes )
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
.

Definition get_row_partial_solve_wit_2 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z)  __default__List_Z (PreH1 : (i >= rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (0 <= rows_pre)) (PreH5 : (rows_pre <= 100)) (PreH6 : ((Zlength (matrix)) = rows_pre)) (PreH7 : ((Zlength (sizes)) = rows_pre)) (PreH8 : (row_sizes_match_87 matrix sizes )) (PreH9 : (problem_87_pre_z matrix x_pre )) (PreH10 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH11 : (0 <= total)) (PreH12 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH13 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (i >= rows_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (i))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
.

Definition get_row_partial_solve_wit_3_pure := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : ((Zlength (matrix)) = rows_pre)) (PreH8 : ((Zlength (sizes)) = rows_pre)) (PreH9 : (row_sizes_match_87 matrix sizes )) (PreH10 : (problem_87_pre_z matrix x_pre )) (PreH11 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH12 : (0 <= total)) (PreH13 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH14 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (((total * 2 ) + 2 ) >= 0) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ”
.

Definition get_row_partial_solve_wit_3_aux := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (total: Z) (i: Z) (retval: Z)  __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : ((Zlength (matrix)) = rows_pre)) (PreH8 : ((Zlength (sizes)) = rows_pre)) (PreH9 : (row_sizes_match_87 matrix sizes )) (PreH10 : (problem_87_pre_z matrix x_pre )) (PreH11 : (total = (total_cells_prefix_87 (matrix) (i)))) (PreH12 : (0 <= total)) (PreH13 : (total <= (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH14 : ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (((total * 2 ) + 2 ) >= 0) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (i >= rows_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (i))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ ((((total_cells_prefix_87 (matrix) (rows_pre)) * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.full lst_pre rows_pre matrix )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
.

Definition get_row_partial_solve_wit_3 := get_row_partial_solve_wit_3_pure -> get_row_partial_solve_wit_3_aux.

Definition get_row_partial_solve_wit_4 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= rows_pre)) (PreH4 : (rows_pre <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_len = (output_size * 2 ))) (PreH8 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH9 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH10 : ((Zlength (matrix)) = rows_pre)) (PreH11 : ((Zlength (sizes)) = rows_pre)) (PreH12 : (row_sizes_match_87 matrix sizes )) (PreH13 : (problem_87_pre_z matrix x_pre )) (PreH14 : (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l )) (PreH15 : (out_len = (Zlength (output_l)))) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= (total + 1 ))) (PreH18 : (0 <= out_len)) (PreH19 : (out_len <= ((total * 2 ) + 2 ))) (PreH20 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH21 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH22 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (scan_state_87 matrix x_pre i ((Znth i sizes 0) - 1 ) output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (((row_sizes_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i sizes 0))
  **  (IntArray.missing_i row_sizes_pre i 0 rows_pre sizes )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
.

Definition get_row_partial_solve_wit_5 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (total: Z) (output_size: Z) (out_len: Z) (data: Z) (out: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= 0)) (PreH2 : ((-1) <= j)) (PreH3 : (j < (Znth i sizes 0))) (PreH4 : (0 <= i)) (PreH5 : (i < rows_pre)) (PreH6 : (0 <= rows_pre)) (PreH7 : (rows_pre <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((Zlength (matrix)) = rows_pre)) (PreH14 : ((Zlength (sizes)) = rows_pre)) (PreH15 : (row_sizes_match_87 matrix sizes )) (PreH16 : (problem_87_pre_z matrix x_pre )) (PreH17 : (scan_state_87 matrix x_pre i j output_l )) (PreH18 : (out_len = (Zlength (output_l)))) (PreH19 : (0 <= output_size)) (PreH20 : (output_size <= (total + 1 ))) (PreH21 : (0 <= out_len)) (PreH22 : (out_len <= ((total * 2 ) + 2 ))) (PreH23 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH24 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH25 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (j >= 0) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ (scan_state_87 matrix x_pre i j output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (((row_ptr + (j * sizeof(INT) ) )) # Int  |-> (Znth j (Znth (i) (matrix) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
.

Definition get_row_partial_solve_wit_6 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
  **  (IntArray.undef_seg data out_len ((total * 2 ) + 2 ) )
|--
  “ (0 <= j) ” 
  &&  “ (j < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((out_len + 1 ) < ((total * 2 ) + 2 )) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ (scan_state_87 matrix x_pre i j output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (((data + (out_len * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (out_len + 1 ) ((total * 2 ) + 2 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
  **  (IntArray.seg data 0 out_len output_l )
.

Definition get_row_partial_solve_wit_7 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (sizes: (@list Z)) (matrix: (@list (@list Z))) (row_ptr: Z) (output_l: (@list Z)) (j: Z) (i: Z) (out: Z) (data: Z) (out_len: Z) (output_size: Z) (total: Z)  __default__List_Z (PreH1 : (0 <= j)) (PreH2 : (j < (Znth i sizes 0))) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : (0 <= rows_pre)) (PreH6 : (rows_pre <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre)) (PreH10 : (out_len = (output_size * 2 ))) (PreH11 : (total = (total_cells_prefix_87 (matrix) (rows_pre)))) (PreH12 : (((total * 2 ) + 2 ) < INT_MAX)) (PreH13 : ((out_len + 1 ) < ((total * 2 ) + 2 ))) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= (total + 1 ))) (PreH16 : (0 <= out_len)) (PreH17 : (out_len <= ((total * 2 ) + 2 ))) (PreH18 : ((Zlength (matrix)) = rows_pre)) (PreH19 : ((Zlength (sizes)) = rows_pre)) (PreH20 : (row_sizes_match_87 matrix sizes )) (PreH21 : (problem_87_pre_z matrix x_pre )) (PreH22 : ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0))) (PreH23 : (scan_state_87 matrix x_pre i j output_l )) (PreH24 : (out_len = (Zlength (output_l)))) (PreH25 : forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100)))) (PreH26 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX)))) ,
  (IntArray.seg data 0 (out_len + 1 ) (app (output_l) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data (out_len + 1 ) ((total * 2 ) + 2 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
|--
  “ (0 <= j) ” 
  &&  “ (j < (Znth i sizes 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth (j) ((Znth (i) (matrix) ((@nil Z)))) (0)) = x_pre) ” 
  &&  “ (out_len = (output_size * 2 )) ” 
  &&  “ (total = (total_cells_prefix_87 (matrix) (rows_pre))) ” 
  &&  “ (((total * 2 ) + 2 ) < INT_MAX) ” 
  &&  “ ((out_len + 1 ) < ((total * 2 ) + 2 )) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (total + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= ((total * 2 ) + 2 )) ” 
  &&  “ ((Zlength (matrix)) = rows_pre) ” 
  &&  “ ((Zlength (sizes)) = rows_pre) ” 
  &&  “ (row_sizes_match_87 matrix sizes ) ” 
  &&  “ (problem_87_pre_z matrix x_pre ) ” 
  &&  “ ((Zlength ((Znth (i) (matrix) ((@nil Z))))) = (Znth i sizes 0)) ” 
  &&  “ (scan_state_87 matrix x_pre i j output_l ) ” 
  &&  “ (out_len = (Zlength (output_l))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < rows_pre)) -> ((0 <= (Znth r sizes 0)) /\ ((Znth r sizes 0) <= 100))) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < rows_pre)) /\ (0 <= c)) /\ (c < (Znth r_2 sizes 0))) -> ((INT_MIN <= (Znth c (Znth r_2 matrix __default__List_Z) 0)) /\ ((Znth c (Znth r_2 matrix __default__List_Z) 0) <= INT_MAX))) ”
  &&  (((data + ((out_len + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data ((out_len + 1 ) + 1 ) ((total * 2 ) + 2 ) )
  **  (IntArray.seg data 0 (out_len + 1 ) (app (output_l) ((cons (i) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr matrix )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (matrix) ((@nil Z))))) (Znth (i) (matrix) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre sizes )
.

Module Type VC_Correct.

Include int_ptr_array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_get_row_safety_wit_1 : get_row_safety_wit_1.
Axiom proof_of_get_row_safety_wit_2 : get_row_safety_wit_2.
Axiom proof_of_get_row_safety_wit_3 : get_row_safety_wit_3.
Axiom proof_of_get_row_safety_wit_4 : get_row_safety_wit_4.
Axiom proof_of_get_row_safety_wit_5 : get_row_safety_wit_5.
Axiom proof_of_get_row_safety_wit_6 : get_row_safety_wit_6.
Axiom proof_of_get_row_safety_wit_7 : get_row_safety_wit_7.
Axiom proof_of_get_row_safety_wit_8 : get_row_safety_wit_8.
Axiom proof_of_get_row_safety_wit_9 : get_row_safety_wit_9.
Axiom proof_of_get_row_safety_wit_10 : get_row_safety_wit_10.
Axiom proof_of_get_row_safety_wit_11 : get_row_safety_wit_11.
Axiom proof_of_get_row_safety_wit_12 : get_row_safety_wit_12.
Axiom proof_of_get_row_safety_wit_13 : get_row_safety_wit_13.
Axiom proof_of_get_row_safety_wit_14 : get_row_safety_wit_14.
Axiom proof_of_get_row_safety_wit_15 : get_row_safety_wit_15.
Axiom proof_of_get_row_safety_wit_16 : get_row_safety_wit_16.
Axiom proof_of_get_row_safety_wit_17 : get_row_safety_wit_17.
Axiom proof_of_get_row_safety_wit_18 : get_row_safety_wit_18.
Axiom proof_of_get_row_safety_wit_19 : get_row_safety_wit_19.
Axiom proof_of_get_row_safety_wit_20 : get_row_safety_wit_20.
Axiom proof_of_get_row_safety_wit_21 : get_row_safety_wit_21.
Axiom proof_of_get_row_safety_wit_22 : get_row_safety_wit_22.
Axiom proof_of_get_row_safety_wit_23 : get_row_safety_wit_23.
Axiom proof_of_get_row_safety_wit_24 : get_row_safety_wit_24.
Axiom proof_of_get_row_safety_wit_25 : get_row_safety_wit_25.
Axiom proof_of_get_row_safety_wit_26 : get_row_safety_wit_26.
Axiom proof_of_get_row_entail_wit_1 : get_row_entail_wit_1.
Axiom proof_of_get_row_entail_wit_2 : get_row_entail_wit_2.
Axiom proof_of_get_row_entail_wit_3 : get_row_entail_wit_3.
Axiom proof_of_get_row_entail_wit_4 : get_row_entail_wit_4.
Axiom proof_of_get_row_entail_wit_5 : get_row_entail_wit_5.
Axiom proof_of_get_row_entail_wit_6 : get_row_entail_wit_6.
Axiom proof_of_get_row_entail_wit_7_1 : get_row_entail_wit_7_1.
Axiom proof_of_get_row_entail_wit_7_2 : get_row_entail_wit_7_2.
Axiom proof_of_get_row_entail_wit_8 : get_row_entail_wit_8.
Axiom proof_of_get_row_entail_wit_9 : get_row_entail_wit_9.
Axiom proof_of_get_row_return_wit_1 : get_row_return_wit_1.
Axiom proof_of_get_row_partial_solve_wit_1 : get_row_partial_solve_wit_1.
Axiom proof_of_get_row_partial_solve_wit_2 : get_row_partial_solve_wit_2.
Axiom proof_of_get_row_partial_solve_wit_3_pure : get_row_partial_solve_wit_3_pure.
Axiom proof_of_get_row_partial_solve_wit_3 : get_row_partial_solve_wit_3.
Axiom proof_of_get_row_partial_solve_wit_4 : get_row_partial_solve_wit_4.
Axiom proof_of_get_row_partial_solve_wit_5 : get_row_partial_solve_wit_5.
Axiom proof_of_get_row_partial_solve_wit_6 : get_row_partial_solve_wit_6.
Axiom proof_of_get_row_partial_solve_wit_7 : get_row_partial_solve_wit_7.

End VC_Correct.
