Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
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
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_120.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function maximum -----*)

Definition maximum_safety_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition maximum_safety_wit_2 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition maximum_safety_wit_3 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition maximum_safety_wit_4 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (k_pre <= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition maximum_safety_wit_5 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (k_pre <= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.undef_full retval_2 0 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition maximum_safety_wit_6 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (k_pre > 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 arr_size_pre )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition maximum_safety_wit_7 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (tmp: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (i = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) (i))) |]
  &&  (((tmp + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 i tmp_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition maximum_safety_wit_8 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (tmp: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition maximum_safety_wit_9 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (tmp: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full retval k_pre )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition maximum_safety_wit_10 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (tmp: Z) (out: Z) ,
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (i))) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i k_pre )
|--
  [| (((arr_size_pre - k_pre ) + i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((arr_size_pre - k_pre ) + i )) |]
.

Definition maximum_safety_wit_11 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (tmp: Z) (out: Z) ,
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (i))) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i k_pre )
|--
  [| ((arr_size_pre - k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (arr_size_pre - k_pre )) |]
.

Definition maximum_safety_wit_12 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (tmp: Z) (out: Z) ,
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth ((arr_size_pre - k_pre ) + i ) sorted_l 0))
  **  (IntArray.undef_seg data (i + 1 ) k_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 i output_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition maximum_entail_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (k_pre > 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  EX (tmp_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (0 = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) (0))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 0 tmp_l )
  **  (IntArray.undef_seg retval_2 0 arr_size_pre )
.

Definition maximum_entail_wit_2 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l_2: (@list Z)) (i: Z) (tmp: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (i = (Zlength (tmp_l_2))) |] 
  &&  [| (tmp_l_2 = (copy_prefix (input_l) (i))) |]
  &&  (((tmp + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 i tmp_l_2 )
|--
  EX (tmp_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| ((i + 1 ) = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) ((i + 1 )))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 (i + 1 ) tmp_l )
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
.

Definition maximum_entail_wit_3 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (tmp: Z) (out: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (i = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) (i))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
|--
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
.

Definition maximum_entail_wit_4 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (tmp: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) ,
  [| (arr_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| ((sublist (0) (arr_size_pre) (sorted_full_l)) = sorted_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.full tmp arr_size_pre sorted_full_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
.

Definition maximum_entail_wit_5 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (tmp: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |]
  &&  (IntArray.undef_full retval k_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
|--
  EX (output_l: (@list Z))  (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (0))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.seg retval 0 0 output_l )
  **  (IntArray.undef_seg retval 0 k_pre )
.

Definition maximum_entail_wit_6 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (sorted_l_2: (@list Z)) (data: Z) (tmp: Z) (out: Z) ,
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (maximum_output_prefix (sorted_l_2) (arr_size_pre) (k_pre) (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth ((arr_size_pre - k_pre ) + i ) sorted_l_2 0))
  **  (IntArray.undef_seg data (i + 1 ) k_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 i output_l_2 )
|--
  EX (output_l: (@list Z))  (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= k_pre) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) ((i + 1 )))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) k_pre )
.

Definition maximum_entail_wit_7 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (sorted_l_2: (@list Z)) (data: Z) (tmp: Z) (out: Z) ,
  [| (i >= k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (maximum_output_prefix (sorted_l_2) (arr_size_pre) (k_pre) (i))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (IntArray.seg data 0 i output_l_2 )
  **  (IntArray.undef_seg data i k_pre )
|--
  EX (output_l: (@list Z))  (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (k_pre = (Zlength (output_l))) |] 
  &&  [| (problem_120_spec_z input_l k_pre output_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> k_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.full data k_pre output_l )
.

Definition maximum_return_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (tmp: Z) (data_2: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (k_pre = (Zlength (output_l_2))) |] 
  &&  [| (problem_120_spec_z input_l k_pre output_l_2 ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.full data_2 k_pre output_l_2 )
|--
  EX (output_l: (@list Z))  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (k_pre = (Zlength (output_l))) |] 
  &&  [| (problem_120_spec_z input_l k_pre output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.full data k_pre output_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition maximum_return_wit_2 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (k_pre <= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.undef_full retval_2 0 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  EX (output_l: (@list Z))  (data: Z) ,
  [| (retval <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (k_pre = (Zlength (output_l))) |] 
  &&  [| (problem_120_spec_z input_l k_pre output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.full data k_pre output_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition maximum_partial_solve_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition maximum_partial_solve_wit_2_pure := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (k_pre <= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 >= 0) |] 
  &&  [| (0 < INT_MAX) |]
.

Definition maximum_partial_solve_wit_2_aux := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (k_pre <= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 >= 0) |] 
  &&  [| (0 < INT_MAX) |] 
  &&  [| (k_pre <= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition maximum_partial_solve_wit_2 := maximum_partial_solve_wit_2_pure -> maximum_partial_solve_wit_2_aux.

Definition maximum_partial_solve_wit_3_pure := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (k_pre > 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_size_pre >= 0) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
.

Definition maximum_partial_solve_wit_3_aux := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (k_pre > 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_size_pre >= 0) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (k_pre > 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition maximum_partial_solve_wit_3 := maximum_partial_solve_wit_3_pure -> maximum_partial_solve_wit_3_aux.

Definition maximum_partial_solve_wit_4 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (tmp: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (i = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) (i))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (i = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) (i))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
.

Definition maximum_partial_solve_wit_5 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (tmp: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (i = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) (i))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (i = (Zlength (tmp_l))) |] 
  &&  [| (tmp_l = (copy_prefix (input_l) (i))) |]
  &&  (((tmp + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 i tmp_l )
.

Definition maximum_partial_solve_wit_6_pure := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (tmp: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
|--
  [| (tmp <> 0) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
.

Definition maximum_partial_solve_wit_6_aux := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (tmp: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
|--
  [| (tmp <> 0) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |]
  &&  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition maximum_partial_solve_wit_6 := maximum_partial_solve_wit_6_pure -> maximum_partial_solve_wit_6_aux.

Definition maximum_partial_solve_wit_7_pure := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (tmp: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
|--
  [| (k_pre >= 0) |] 
  &&  [| (k_pre < INT_MAX) |]
.

Definition maximum_partial_solve_wit_7_aux := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (tmp: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
|--
  [| (k_pre >= 0) |] 
  &&  [| (k_pre < INT_MAX) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
.

Definition maximum_partial_solve_wit_7 := maximum_partial_solve_wit_7_pure -> maximum_partial_solve_wit_7_aux.

Definition maximum_partial_solve_wit_8 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (tmp: Z) (out: Z) ,
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (i))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i k_pre )
|--
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (i))) |]
  &&  (((tmp + (((arr_size_pre - k_pre ) + i ) * sizeof(INT) ) )) # Int  |-> (Znth ((arr_size_pre - k_pre ) + i ) sorted_l 0))
  **  (IntArray.missing_i tmp ((arr_size_pre - k_pre ) + i ) 0 arr_size_pre sorted_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i k_pre )
.

Definition maximum_partial_solve_wit_9 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (tmp: Z) (out: Z) ,
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (i))) |]
  &&  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i k_pre )
|--
  [| (i < k_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (output_l = (maximum_output_prefix (sorted_l) (arr_size_pre) (k_pre) (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) k_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 i output_l )
.

Definition maximum_partial_solve_wit_10_pure := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_l: (@list Z)) (out: Z) (tmp: Z) (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (k_pre = (Zlength (output_l))) |] 
  &&  [| (problem_120_spec_z input_l k_pre output_l ) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> k_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.full data k_pre output_l )
|--
  [| (tmp <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |]
.

Definition maximum_partial_solve_wit_10_aux := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_l: (@list Z)) (out: Z) (tmp: Z) (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (k_pre = (Zlength (output_l))) |] 
  &&  [| (problem_120_spec_z input_l k_pre output_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.full data k_pre output_l )
|--
  [| (tmp <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (out <> 0) |] 
  &&  [| (tmp <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (arr_pre <> 0) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre <= 1000) |] 
  &&  [| (0 < k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (arr_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_120_pre_z input_l k_pre ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (k_pre = (Zlength (output_l))) |] 
  &&  [| (problem_120_spec_z input_l k_pre output_l ) |]
  &&  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> k_pre)
  **  (IntArray.full data k_pre output_l )
.

Definition maximum_partial_solve_wit_10 := maximum_partial_solve_wit_10_pure -> maximum_partial_solve_wit_10_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_maximum_safety_wit_1 : maximum_safety_wit_1.
Axiom proof_of_maximum_safety_wit_2 : maximum_safety_wit_2.
Axiom proof_of_maximum_safety_wit_3 : maximum_safety_wit_3.
Axiom proof_of_maximum_safety_wit_4 : maximum_safety_wit_4.
Axiom proof_of_maximum_safety_wit_5 : maximum_safety_wit_5.
Axiom proof_of_maximum_safety_wit_6 : maximum_safety_wit_6.
Axiom proof_of_maximum_safety_wit_7 : maximum_safety_wit_7.
Axiom proof_of_maximum_safety_wit_8 : maximum_safety_wit_8.
Axiom proof_of_maximum_safety_wit_9 : maximum_safety_wit_9.
Axiom proof_of_maximum_safety_wit_10 : maximum_safety_wit_10.
Axiom proof_of_maximum_safety_wit_11 : maximum_safety_wit_11.
Axiom proof_of_maximum_safety_wit_12 : maximum_safety_wit_12.
Axiom proof_of_maximum_entail_wit_1 : maximum_entail_wit_1.
Axiom proof_of_maximum_entail_wit_2 : maximum_entail_wit_2.
Axiom proof_of_maximum_entail_wit_3 : maximum_entail_wit_3.
Axiom proof_of_maximum_entail_wit_4 : maximum_entail_wit_4.
Axiom proof_of_maximum_entail_wit_5 : maximum_entail_wit_5.
Axiom proof_of_maximum_entail_wit_6 : maximum_entail_wit_6.
Axiom proof_of_maximum_entail_wit_7 : maximum_entail_wit_7.
Axiom proof_of_maximum_return_wit_1 : maximum_return_wit_1.
Axiom proof_of_maximum_return_wit_2 : maximum_return_wit_2.
Axiom proof_of_maximum_partial_solve_wit_1 : maximum_partial_solve_wit_1.
Axiom proof_of_maximum_partial_solve_wit_2_pure : maximum_partial_solve_wit_2_pure.
Axiom proof_of_maximum_partial_solve_wit_2 : maximum_partial_solve_wit_2.
Axiom proof_of_maximum_partial_solve_wit_3_pure : maximum_partial_solve_wit_3_pure.
Axiom proof_of_maximum_partial_solve_wit_3 : maximum_partial_solve_wit_3.
Axiom proof_of_maximum_partial_solve_wit_4 : maximum_partial_solve_wit_4.
Axiom proof_of_maximum_partial_solve_wit_5 : maximum_partial_solve_wit_5.
Axiom proof_of_maximum_partial_solve_wit_6_pure : maximum_partial_solve_wit_6_pure.
Axiom proof_of_maximum_partial_solve_wit_6 : maximum_partial_solve_wit_6.
Axiom proof_of_maximum_partial_solve_wit_7_pure : maximum_partial_solve_wit_7_pure.
Axiom proof_of_maximum_partial_solve_wit_7 : maximum_partial_solve_wit_7.
Axiom proof_of_maximum_partial_solve_wit_8 : maximum_partial_solve_wit_8.
Axiom proof_of_maximum_partial_solve_wit_9 : maximum_partial_solve_wit_9.
Axiom proof_of_maximum_partial_solve_wit_10_pure : maximum_partial_solve_wit_10_pure.
Axiom proof_of_maximum_partial_solve_wit_10 : maximum_partial_solve_wit_10.

End VC_Correct.
