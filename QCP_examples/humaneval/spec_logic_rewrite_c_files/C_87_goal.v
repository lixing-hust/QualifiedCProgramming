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
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.

(*----- Function get_row -----*)

Definition get_row_safety_wit_1 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre < INT_MAX)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_2 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre < INT_MAX)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_3 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (i: Z) (count: Z) (row_len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre i count )) (PreH7 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH8 : (0 <= row_len)) (PreH9 : (row_len < INT_MAX)) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((row_len - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (row_len - 1 )) ”
.

Definition get_row_safety_wit_4 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (i: Z) (count: Z) (row_len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre i count )) (PreH7 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH8 : (0 <= row_len)) (PreH9 : (row_len < INT_MAX)) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_5 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : ((-1) <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_inner_87 input_l x_pre i j count )) (PreH9 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH10 : (0 <= row_len)) (PreH11 : (row_len < INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : ((2 * count ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_6 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition get_row_safety_wit_7 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition get_row_safety_wit_8 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition get_row_safety_wit_9 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_inner_87 input_l x_pre i j count )) (PreH10 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH11 : (0 <= row_len)) (PreH12 : (row_len < INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : ((2 * count ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_row_safety_wit_10 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre i count )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((2 * count ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * count )) ”
.

Definition get_row_safety_wit_11 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre i count )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_row_safety_wit_12 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre i count )) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  ((( &( "size" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 (2 * count ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_13 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre i count )) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_2 (2 * count ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_14 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (count: Z) (row_len: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH7 : (fill_scan_outer_87 input_l x_pre i coords )) (PreH8 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH9 : (0 <= row_len)) (PreH10 : (row_len < INT_MAX)) (PreH11 : (0 <= count)) (PreH12 : ((2 * count ) < INT_MAX)) (PreH13 : (0 <= size)) (PreH14 : (size = (Zlength (coords)))) (PreH15 : (size <= count)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((row_len - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (row_len - 1 )) ”
.

Definition get_row_safety_wit_15 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (count: Z) (row_len: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH7 : (fill_scan_outer_87 input_l x_pre i coords )) (PreH8 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH9 : (0 <= row_len)) (PreH10 : (row_len < INT_MAX)) (PreH11 : (0 <= count)) (PreH12 : ((2 * count ) < INT_MAX)) (PreH13 : (0 <= size)) (PreH14 : (size = (Zlength (coords)))) (PreH15 : (size <= count)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_16 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (data: Z) (out: Z) (size: Z) (coords: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : ((-1) <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH11 : (0 <= row_len)) (PreH12 : (row_len < INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : ((2 * count ) < INT_MAX)) (PreH15 : (0 <= size)) (PreH16 : (size = (Zlength (coords)))) (PreH17 : (size <= count)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_row_safety_wit_17 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((2 * size ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * size )) ”
.

Definition get_row_safety_wit_18 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_row_safety_wit_19 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 ((2 * size ) + 1 ) (app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((2 * size ) + 1 ) (2 * count ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (((2 * size ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * size ) + 1 )) ”
.

Definition get_row_safety_wit_20 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 ((2 * size ) + 1 ) (app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((2 * size ) + 1 ) (2 * count ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((2 * size ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * size )) ”
.

Definition get_row_safety_wit_21 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 ((2 * size ) + 1 ) (app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((2 * size ) + 1 ) (2 * count ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_row_safety_wit_22 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 ((2 * size ) + 1 ) (app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((2 * size ) + 1 ) (2 * count ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_row_safety_wit_23 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 (((2 * size ) + 1 ) + 1 ) (app ((app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data (((2 * size ) + 1 ) + 1 ) (2 * count ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (size + 1 )) ”
.

Definition get_row_safety_wit_24 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 (((2 * size ) + 1 ) + 1 ) (app ((app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data (((2 * size ) + 1 ) + 1 ) (2 * count ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition get_row_safety_wit_25 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (data: Z) (out: Z) (size: Z) (coords: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH11 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH12 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH13 : (0 <= row_len)) (PreH14 : (row_len < INT_MAX)) (PreH15 : (0 <= count)) (PreH16 : ((2 * count ) < INT_MAX)) (PreH17 : (0 <= size)) (PreH18 : (size = (Zlength (coords)))) (PreH19 : (size <= count)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) ,
  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "row_len" ) )) # Int  |-> row_len)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition get_row_safety_wit_26 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (data: Z) (out: Z) (size: Z) (coords: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH10 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size <= count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_row_entail_wit_1 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre < INT_MAX)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) ,
  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre 0 0 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((2 * 0 ) < INT_MAX) ”
  &&  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre < INT_MAX)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) ,
  TT && emp 
|--
  “ (count_scan_outer_87 input_l x_pre 0 0 ) ”
  &&  emp
).

Definition get_row_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (PreH1 : (0 <= rows_pre)) (PreH2 : (rows_pre < INT_MAX)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) ,
  TT && emp 
|--
  “ (count_scan_outer_87 input_l x_pre 0 0 ) ”
.

Definition get_row_entail_wit_2 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre i count ) ” 
  &&  “ ((Znth i (row_sizes_87 (input_l)) 0) = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= (Znth i (row_sizes_87 (input_l)) 0)) ” 
  &&  “ ((Znth i (row_sizes_87 (input_l)) 0) < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Znth i (row_sizes_87 (input_l)) 0) (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i input_l __default__List_Z))) (Znth i input_l __default__List_Z) )
|--
  “ ((Znth i (row_sizes_87 (input_l)) 0) < INT_MAX) ” 
  &&  “ (0 <= (Znth i (row_sizes_87 (input_l)) 0)) ” 
  &&  “ ((Znth i (row_sizes_87 (input_l)) 0) = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ”
  &&  (IntArray.full row_ptr_2 (Znth i (row_sizes_87 (input_l)) 0) (Znth (i) (input_l) ((@nil Z))) )
).

Definition get_row_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i input_l __default__List_Z))) (Znth i input_l __default__List_Z) )
|--
  “ ((Znth i (row_sizes_87 (input_l)) 0) < INT_MAX) ”
.

Definition get_row_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i input_l __default__List_Z))) (Znth i input_l __default__List_Z) )
|--
  “ (0 <= (Znth i (row_sizes_87 (input_l)) 0)) ”
.

Definition get_row_entail_wit_2_split_goal_3 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i input_l __default__List_Z))) (Znth i input_l __default__List_Z) )
|--
  “ ((Znth i (row_sizes_87 (input_l)) 0) = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ”
.

Definition get_row_entail_wit_2_split_goal_spatial := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i input_l __default__List_Z))) (Znth i input_l __default__List_Z) )
|--
  (IntArray.full row_ptr_2 (Znth i (row_sizes_87 (input_l)) 0) (Znth (i) (input_l) ((@nil Z))) )
.

Definition get_row_entail_wit_3 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr_2: Z) (i: Z) (count: Z) (row_len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre i count )) (PreH7 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH8 : (0 <= row_len)) (PreH9 : (row_len < INT_MAX)) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (row_len - 1 )) ” 
  &&  “ ((row_len - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_inner_87 input_l x_pre i (row_len - 1 ) count ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (i: Z) (count: Z) (row_len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre i count )) (PreH7 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH8 : (0 <= row_len)) (PreH9 : (row_len < INT_MAX)) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  TT && emp 
|--
  “ (count_scan_inner_87 input_l x_pre i (row_len - 1 ) count ) ”
  &&  emp
).

Definition get_row_entail_wit_3_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (i: Z) (count: Z) (row_len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre i count )) (PreH7 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH8 : (0 <= row_len)) (PreH9 : (row_len < INT_MAX)) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  TT && emp 
|--
  “ (count_scan_inner_87 input_l x_pre i (row_len - 1 ) count ) ”
.

Definition get_row_entail_wit_4_1 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr_2: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr_2 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_inner_87 input_l x_pre i (j - 1 ) (count + 1 ) ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((2 * (count + 1 ) ) < INT_MAX) ”
  &&  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  TT && emp 
|--
  “ ((2 * (count + 1 ) ) < INT_MAX) ” 
  &&  “ (count_scan_inner_87 input_l x_pre i (j - 1 ) (count + 1 ) ) ”
  &&  emp
).

Definition get_row_entail_wit_4_1_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  TT && emp 
|--
  “ ((2 * (count + 1 ) ) < INT_MAX) ”
.

Definition get_row_entail_wit_4_1_split_goal_2 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  TT && emp 
|--
  “ (count_scan_inner_87 input_l x_pre i (j - 1 ) (count + 1 ) ) ”
.

Definition get_row_entail_wit_4_2 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr_2: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  (IntArray.full row_ptr_2 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_inner_87 input_l x_pre i (j - 1 ) count ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  TT && emp 
|--
  “ (count_scan_inner_87 input_l x_pre i (j - 1 ) count ) ”
  &&  emp
).

Definition get_row_entail_wit_4_2_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_inner_87 input_l x_pre i j count )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) ,
  TT && emp 
|--
  “ (count_scan_inner_87 input_l x_pre i (j - 1 ) count ) ”
.

Definition get_row_entail_wit_5 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_inner_87 input_l x_pre i j count )) (PreH10 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH11 : (0 <= row_len)) (PreH12 : (row_len < INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre (i + 1 ) count ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_inner_87 input_l x_pre i j count )) (PreH10 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH11 : (0 <= row_len)) (PreH12 : (row_len < INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
|--
  “ (count_scan_outer_87 input_l x_pre (i + 1 ) count ) ”
  &&  (IntPtrArray2.full lst_pre rows_pre input_l )
).

Definition get_row_entail_wit_5_split_goal_1 := 
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_inner_87 input_l x_pre i j count )) (PreH10 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH11 : (0 <= row_len)) (PreH12 : (row_len < INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
|--
  “ (count_scan_outer_87 input_l x_pre (i + 1 ) count ) ”
.

Definition get_row_entail_wit_5_split_goal_spatial := 
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_inner_87 input_l x_pre i j count )) (PreH10 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH11 : (0 <= row_len)) (PreH12 : (row_len < INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
|--
  (IntPtrArray2.full lst_pre rows_pre input_l )
.

Definition get_row_entail_wit_6 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre i count )) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  (IntArray.undef_full retval_2 (2 * count ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre 0 coords ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (coords))) ” 
  &&  “ (0 <= count) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.seg retval_2 0 (2 * 0 ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg retval_2 (2 * 0 ) (2 * count ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (i >= rows_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= rows_pre)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre i count )) (PreH10 : (0 <= count)) (PreH11 : ((2 * count ) < INT_MAX)) ,
  (IntArray.undef_full retval_2 (2 * count ) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre 0 coords ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (coords))) ” 
  &&  “ (0 <= count) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.seg retval_2 0 (2 * 0 ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg retval_2 (2 * 0 ) (2 * count ) )
).

Definition get_row_entail_wit_7 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (i: Z) (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH8 : (fill_scan_outer_87 input_l x_pre i coords_2 )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) (PreH11 : (0 <= size)) (PreH12 : (size = (Zlength (coords_2)))) (PreH13 : (size <= count)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords_2)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
|--
  EX (row_ptr: Z)  (coords: (@list (Z * Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre i coords ) ” 
  &&  “ ((Znth i (row_sizes_87 (input_l)) 0) = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= (Znth i (row_sizes_87 (input_l)) 0)) ” 
  &&  “ ((Znth i (row_sizes_87 (input_l)) 0) < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Znth i (row_sizes_87 (input_l)) 0) (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH8 : (fill_scan_outer_87 input_l x_pre i coords_2 )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) (PreH11 : (0 <= size)) (PreH12 : (size = (Zlength (coords_2)))) (PreH13 : (size <= count)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i input_l __default__List_Z))) (Znth i input_l __default__List_Z) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ ((coords_flat_87 (coords_2)) = (coords_flat_87 (coords))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre i coords ) ” 
  &&  “ ((Znth i (row_sizes_87 (input_l)) 0) = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= (Znth i (row_sizes_87 (input_l)) 0)) ” 
  &&  “ ((Znth i (row_sizes_87 (input_l)) 0) < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.full row_ptr_2 (Znth i (row_sizes_87 (input_l)) 0) (Znth (i) (input_l) ((@nil Z))) )
).

Definition get_row_entail_wit_8 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr_2: Z) (coords_2: (@list (Z * Z))) (i: Z) (count: Z) (row_len: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH7 : (fill_scan_outer_87 input_l x_pre i coords_2 )) (PreH8 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH9 : (0 <= row_len)) (PreH10 : (row_len < INT_MAX)) (PreH11 : (0 <= count)) (PreH12 : ((2 * count ) < INT_MAX)) (PreH13 : (0 <= size)) (PreH14 : (size = (Zlength (coords_2)))) (PreH15 : (size <= count)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords_2)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (row_ptr: Z)  (coords: (@list (Z * Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (row_len - 1 )) ” 
  &&  “ ((row_len - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i (row_len - 1 ) coords ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (coords_2: (@list (Z * Z))) (i: Z) (count: Z) (row_len: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (rows_pre = (Zlength (input_l)))) (PreH4 : (problem_87_pre_z input_l x_pre )) (PreH5 : (get_row_safe_87 input_l )) (PreH6 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH7 : (fill_scan_outer_87 input_l x_pre i coords_2 )) (PreH8 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH9 : (0 <= row_len)) (PreH10 : (row_len < INT_MAX)) (PreH11 : (0 <= count)) (PreH12 : ((2 * count ) < INT_MAX)) (PreH13 : (0 <= size)) (PreH14 : (size = (Zlength (coords_2)))) (PreH15 : (size <= count)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  TT && emp 
|--
  EX (coords: (@list (Z * Z))) ,
  “ ((coords_flat_87 (coords_2)) = (coords_flat_87 (coords))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (row_len - 1 )) ” 
  &&  “ ((row_len - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i (row_len - 1 ) coords ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  emp
).

Definition get_row_entail_wit_9 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr_2: Z) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH11 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH12 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH13 : (0 <= row_len)) (PreH14 : (row_len < INT_MAX)) (PreH15 : (0 <= count)) (PreH16 : ((2 * count ) < INT_MAX)) (PreH17 : (0 <= size)) (PreH18 : (size = (Zlength (coords_2)))) (PreH19 : (size <= count)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) ,
  (IntArray.full row_ptr_2 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords_2)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (row_ptr: Z)  (coords: (@list (Z * Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i j coords ) ” 
  &&  “ ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size < count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) = x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH11 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH12 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH13 : (0 <= row_len)) (PreH14 : (row_len < INT_MAX)) (PreH15 : (0 <= count)) (PreH16 : ((2 * count ) < INT_MAX)) (PreH17 : (0 <= size)) (PreH18 : (size = (Zlength (coords_2)))) (PreH19 : (size <= count)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) ,
  TT && emp 
|--
  EX (coords: (@list (Z * Z))) ,
  “ ((coords_flat_87 (coords_2)) = (coords_flat_87 (coords))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i j coords ) ” 
  &&  “ ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size < count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  emp
).

Definition get_row_entail_wit_10_1 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr_2: Z) (coords_2: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords_2)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 (((2 * size ) + 1 ) + 1 ) (app ((app ((coords_flat_87 (coords_2))) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
  **  (IntArray.undef_seg data (((2 * size ) + 1 ) + 1 ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (row_ptr: Z)  (coords: (@list (Z * Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i (j - 1 ) coords ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= (size + 1 )) ” 
  &&  “ ((size + 1 ) = (Zlength (coords))) ” 
  &&  “ ((size + 1 ) <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.seg data 0 (2 * (size + 1 ) ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * (size + 1 ) ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (coords_2: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords_2)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 (((2 * size ) + 1 ) + 1 ) (app ((app ((coords_flat_87 (coords_2))) ((cons (i) ((@nil Z)))))) ((cons (j) ((@nil Z))))) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i (j - 1 ) coords ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= (size + 1 )) ” 
  &&  “ ((size + 1 ) = (Zlength (coords))) ” 
  &&  “ ((size + 1 ) <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.seg data 0 (2 * (size + 1 ) ) (coords_flat_87 (coords)) )
).

Definition get_row_entail_wit_10_2 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr_2: Z) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH11 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH12 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH13 : (0 <= row_len)) (PreH14 : (row_len < INT_MAX)) (PreH15 : (0 <= count)) (PreH16 : ((2 * count ) < INT_MAX)) (PreH17 : (0 <= size)) (PreH18 : (size = (Zlength (coords_2)))) (PreH19 : (size <= count)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) ,
  (IntArray.full row_ptr_2 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords_2)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr_2 input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (row_ptr: Z)  (coords: (@list (Z * Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i (j - 1 ) coords ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (Znth (i) (input_l) ((@nil Z))) 0) <> x_pre)) (PreH2 : (j >= 0)) (PreH3 : (0 <= i)) (PreH4 : (i < rows_pre)) (PreH5 : ((-1) <= j)) (PreH6 : (j < row_len)) (PreH7 : (rows_pre = (Zlength (input_l)))) (PreH8 : (problem_87_pre_z input_l x_pre )) (PreH9 : (get_row_safe_87 input_l )) (PreH10 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH11 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH12 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH13 : (0 <= row_len)) (PreH14 : (row_len < INT_MAX)) (PreH15 : (0 <= count)) (PreH16 : ((2 * count ) < INT_MAX)) (PreH17 : (0 <= size)) (PreH18 : (size = (Zlength (coords_2)))) (PreH19 : (size <= count)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) ,
  TT && emp 
|--
  EX (coords: (@list (Z * Z))) ,
  “ ((coords_flat_87 (coords_2)) = (coords_flat_87 (coords))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i (j - 1 ) coords ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  emp
).

Definition get_row_entail_wit_11 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH10 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords_2)))) (PreH18 : (size <= count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords_2)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre (i + 1 ) coords ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH10 : (fill_scan_inner_87 input_l x_pre i j coords_2 )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords_2)))) (PreH18 : (size <= count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ ((coords_flat_87 (coords_2)) = (coords_flat_87 (coords))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre (i + 1 ) coords ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntPtrArray2.full lst_pre rows_pre input_l )
).

Definition get_row_entail_wit_12 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (i: Z) (PreH1 : (i >= rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH8 : (fill_scan_outer_87 input_l x_pre i coords_2 )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) (PreH11 : (0 <= size)) (PreH12 : (size = (Zlength (coords_2)))) (PreH13 : (size <= count)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords_2)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre rows_pre coords ) ” 
  &&  “ (get_row_finished_87 input_l x_pre coords ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size = count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.full data (2 * size ) (coords_flat_87 (coords)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (data: Z) (out: Z) (size: Z) (coords_2: (@list (Z * Z))) (count: Z) (i: Z) (PreH1 : (i >= rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH8 : (fill_scan_outer_87 input_l x_pre i coords_2 )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) (PreH11 : (0 <= size)) (PreH12 : (size = (Zlength (coords_2)))) (PreH13 : (size <= count)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords_2)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre rows_pre coords ) ” 
  &&  “ (get_row_finished_87 input_l x_pre coords ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size = count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (IntArray.full data (2 * size ) (coords_flat_87 (coords)) )
).

Definition get_row_return_wit_1 := 
(
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (coords_2: (@list (Z * Z))) (count: Z) (size_2: Z) (out: Z) (data_2: Z) (PreH1 : (rows_pre = (Zlength (input_l)))) (PreH2 : (problem_87_pre_z input_l x_pre )) (PreH3 : (get_row_safe_87 input_l )) (PreH4 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH5 : (fill_scan_outer_87 input_l x_pre rows_pre coords_2 )) (PreH6 : (get_row_finished_87 input_l x_pre coords_2 )) (PreH7 : (0 <= count)) (PreH8 : ((2 * count ) < INT_MAX)) (PreH9 : (0 <= size_2)) (PreH10 : (size_2 = (Zlength (coords_2)))) (PreH11 : (size_2 = count)) (PreH12 : (out <> 0)) (PreH13 : (data_2 <> 0)) ,
  (IntArray.full data_2 (2 * size_2 ) (coords_flat_87 (coords_2)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size_2)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  EX (coords: (@list (Z * Z)))  (data_l: (@list Z))  (size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ ((2 * size ) = (Zlength (data_l))) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ ((coords_flat_87 (coords)) = data_l) ” 
  &&  “ (problem_87_spec_z input_l x_pre coords ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.full data (2 * size ) data_l )
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
) \/
(
forall (x_pre: Z) (rows_pre: Z) (input_l: (@list (@list Z))) (coords_2: (@list (Z * Z))) (count: Z) (size_2: Z) (out: Z) (data_2: Z) (PreH1 : (rows_pre = (Zlength (input_l)))) (PreH2 : (problem_87_pre_z input_l x_pre )) (PreH3 : (get_row_safe_87 input_l )) (PreH4 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH5 : (fill_scan_outer_87 input_l x_pre rows_pre coords_2 )) (PreH6 : (get_row_finished_87 input_l x_pre coords_2 )) (PreH7 : (0 <= count)) (PreH8 : ((2 * count ) < INT_MAX)) (PreH9 : (0 <= size_2)) (PreH10 : (size_2 = (Zlength (coords_2)))) (PreH11 : (size_2 = count)) (PreH12 : (out <> 0)) (PreH13 : (data_2 <> 0)) ,
  (IntArray.full data_2 (2 * size_2 ) (coords_flat_87 (coords_2)) )
|--
  EX (coords: (@list (Z * Z))) ,
  “ (size_2 = (Zlength (coords))) ” 
  &&  “ (size_2 = (Zlength (coords))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 <= (Zlength (coords))) ” 
  &&  “ ((2 * (Zlength (coords)) ) = (Zlength ((coords_flat_87 (coords))))) ” 
  &&  “ (problem_87_spec_z input_l x_pre coords ) ”
  &&  (IntArray.full data_2 (2 * (Zlength (coords)) ) (coords_flat_87 (coords)) )
).

Definition get_row_partial_solve_wit_1 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (i < rows_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre i count ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  (((row_sizes_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i (row_sizes_87 (input_l)) 0))
  **  (IntArray.missing_i row_sizes_pre i 0 rows_pre (row_sizes_87 (input_l)) )
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
.

Definition get_row_partial_solve_wit_2 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j >= 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_inner_87 input_l x_pre i j count )) (PreH10 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH11 : (0 <= row_len)) (PreH12 : (row_len < INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (j >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_inner_87 input_l x_pre i j count ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  (((row_ptr + (j * sizeof(INT) ) )) # Int  |-> (Znth j (Znth (i) (input_l) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr j 0 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
.

Definition get_row_partial_solve_wit_3 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (PreH1 : (i >= rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre i count )) (PreH8 : (0 <= count)) (PreH9 : ((2 * count ) < INT_MAX)) ,
  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (i >= rows_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre i count ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
.

Definition get_row_partial_solve_wit_4_pure := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre i count )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "row_sizes" ) )) # Ptr  |-> row_sizes_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= (2 * count )) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
.

Definition get_row_partial_solve_wit_4_aux := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (count: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= rows_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= rows_pre)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre i count )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= (2 * count )) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (i >= rows_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre i count ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
.

Definition get_row_partial_solve_wit_4 := get_row_partial_solve_wit_4_pure -> get_row_partial_solve_wit_4_aux.

Definition get_row_partial_solve_wit_5 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (data: Z) (out: Z) (size: Z) (coords: (@list (Z * Z))) (count: Z) (i: Z) (PreH1 : (i < rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= rows_pre)) (PreH4 : (rows_pre = (Zlength (input_l)))) (PreH5 : (problem_87_pre_z input_l x_pre )) (PreH6 : (get_row_safe_87 input_l )) (PreH7 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH8 : (fill_scan_outer_87 input_l x_pre i coords )) (PreH9 : (0 <= count)) (PreH10 : ((2 * count ) < INT_MAX)) (PreH11 : (0 <= size)) (PreH12 : (size = (Zlength (coords)))) (PreH13 : (size <= count)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (i < rows_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= rows_pre) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_outer_87 input_l x_pre i coords ) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((row_sizes_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i (row_sizes_87 (input_l)) 0))
  **  (IntArray.missing_i row_sizes_pre i 0 rows_pre (row_sizes_87 (input_l)) )
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.full lst_pre rows_pre input_l )
.

Definition get_row_partial_solve_wit_6 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (data: Z) (out: Z) (size: Z) (coords: (@list (Z * Z))) (count: Z) (row_len: Z) (j: Z) (i: Z) (PreH1 : (j >= 0)) (PreH2 : (0 <= i)) (PreH3 : (i < rows_pre)) (PreH4 : ((-1) <= j)) (PreH5 : (j < row_len)) (PreH6 : (rows_pre = (Zlength (input_l)))) (PreH7 : (problem_87_pre_z input_l x_pre )) (PreH8 : (get_row_safe_87 input_l )) (PreH9 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH10 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size <= count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (j >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i j coords ) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size <= count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((row_ptr + (j * sizeof(INT) ) )) # Int  |-> (Znth j (Znth (i) (input_l) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr j 0 row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
.

Definition get_row_partial_solve_wit_7 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  (IntArray.undef_seg data (2 * size ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i j coords ) ” 
  &&  “ ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size < count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + ((2 * size ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data ((2 * size ) + 1 ) (2 * count ) )
  **  (IntArray.seg data 0 (2 * size ) (coords_flat_87 (coords)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
.

Definition get_row_partial_solve_wit_8 := 
forall (x_pre: Z) (rows_pre: Z) (row_sizes_pre: Z) (lst_pre: Z) (input_l: (@list (@list Z))) (row_ptr: Z) (coords: (@list (Z * Z))) (i: Z) (j: Z) (row_len: Z) (count: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < rows_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < row_len)) (PreH5 : (rows_pre = (Zlength (input_l)))) (PreH6 : (problem_87_pre_z input_l x_pre )) (PreH7 : (get_row_safe_87 input_l )) (PreH8 : (count_scan_outer_87 input_l x_pre rows_pre count )) (PreH9 : (fill_scan_inner_87 input_l x_pre i j coords )) (PreH10 : ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre)) (PreH11 : (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z))))))) (PreH12 : (0 <= row_len)) (PreH13 : (row_len < INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : ((2 * count ) < INT_MAX)) (PreH16 : (0 <= size)) (PreH17 : (size = (Zlength (coords)))) (PreH18 : (size < count)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) ,
  (IntArray.seg data 0 ((2 * size ) + 1 ) (app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg data ((2 * size ) + 1 ) (2 * count ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < rows_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < row_len) ” 
  &&  “ (rows_pre = (Zlength (input_l))) ” 
  &&  “ (problem_87_pre_z input_l x_pre ) ” 
  &&  “ (get_row_safe_87 input_l ) ” 
  &&  “ (count_scan_outer_87 input_l x_pre rows_pre count ) ” 
  &&  “ (fill_scan_inner_87 input_l x_pre i j coords ) ” 
  &&  “ ((Znth (j) ((Znth (i) (input_l) ((@nil Z)))) (0)) = x_pre) ” 
  &&  “ (row_len = (Zlength ((Znth (i) (input_l) ((@nil Z)))))) ” 
  &&  “ (0 <= row_len) ” 
  &&  “ (row_len < INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((2 * count ) < INT_MAX) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size = (Zlength (coords))) ” 
  &&  “ (size < count) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + (((2 * size ) + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (((2 * size ) + 1 ) + 1 ) (2 * count ) )
  **  (IntArray.seg data 0 ((2 * size ) + 1 ) (app ((coords_flat_87 (coords))) ((cons (i) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntPtrArray2.missing_i lst_pre rows_pre i row_ptr input_l )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr row_len (Znth (i) (input_l) ((@nil Z))) )
  **  (IntArray.full row_sizes_pre rows_pre (row_sizes_87 (input_l)) )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include int_ptr_array2_Strategy_Correct.

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
Axiom proof_of_get_row_entail_wit_4_1 : get_row_entail_wit_4_1.
Axiom proof_of_get_row_entail_wit_4_2 : get_row_entail_wit_4_2.
Axiom proof_of_get_row_entail_wit_5 : get_row_entail_wit_5.
Axiom proof_of_get_row_entail_wit_6 : get_row_entail_wit_6.
Axiom proof_of_get_row_entail_wit_7 : get_row_entail_wit_7.
Axiom proof_of_get_row_entail_wit_8 : get_row_entail_wit_8.
Axiom proof_of_get_row_entail_wit_9 : get_row_entail_wit_9.
Axiom proof_of_get_row_entail_wit_10_1 : get_row_entail_wit_10_1.
Axiom proof_of_get_row_entail_wit_10_2 : get_row_entail_wit_10_2.
Axiom proof_of_get_row_entail_wit_11 : get_row_entail_wit_11.
Axiom proof_of_get_row_entail_wit_12 : get_row_entail_wit_12.
Axiom proof_of_get_row_return_wit_1 : get_row_return_wit_1.
Axiom proof_of_get_row_partial_solve_wit_1 : get_row_partial_solve_wit_1.
Axiom proof_of_get_row_partial_solve_wit_2 : get_row_partial_solve_wit_2.
Axiom proof_of_get_row_partial_solve_wit_3 : get_row_partial_solve_wit_3.
Axiom proof_of_get_row_partial_solve_wit_4_pure : get_row_partial_solve_wit_4_pure.
Axiom proof_of_get_row_partial_solve_wit_4 : get_row_partial_solve_wit_4.
Axiom proof_of_get_row_partial_solve_wit_5 : get_row_partial_solve_wit_5.
Axiom proof_of_get_row_partial_solve_wit_6 : get_row_partial_solve_wit_6.
Axiom proof_of_get_row_partial_solve_wit_7 : get_row_partial_solve_wit_7.
Axiom proof_of_get_row_partial_solve_wit_8 : get_row_partial_solve_wit_8.

End VC_Correct.
