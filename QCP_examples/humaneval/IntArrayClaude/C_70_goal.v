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
Require Import coins_70.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function strange_sort_list -----*)

Definition strange_sort_list_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 lst_size_pre )
  **  ((( &( "sorted" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition strange_sort_list_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((sorted + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (copy_prefix (i) (input_l)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition strange_sort_list_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| ((copy_prefix (lst_size_pre) (input_l)) = input_l) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition strange_sort_list_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) ,
  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| ((copy_prefix (lst_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition strange_sort_list_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((i <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition strange_sort_list_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition strange_sort_list_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition strange_sort_list_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((i <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition strange_sort_list_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition strange_sort_list_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (((lst_size_pre - 1 ) - (i ÷ 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) |]
.

Definition strange_sort_list_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((i <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition strange_sort_list_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((lst_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (lst_size_pre - 1 )) |]
.

Definition strange_sort_list_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition strange_sort_list_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition strange_sort_list_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth ((lst_size_pre - 1 ) - (i ÷ 2 ) ) sorted_full_l 0))
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition strange_sort_list_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth (i ÷ 2 ) sorted_full_l 0))
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition strange_sort_list_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  (IntArray.undef_full retval_3 lst_size_pre )
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (0 = (Zlength ((copy_prefix (0) (input_l))))) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.seg retval_3 0 0 (copy_prefix (0) (input_l)) )
  **  (IntArray.undef_seg retval_3 0 lst_size_pre )
.

Definition strange_sort_list_entail_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((sorted + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (copy_prefix (i) (input_l)) )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| ((i + 1 ) = (Zlength ((copy_prefix ((i + 1 )) (input_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 (i + 1 ) (copy_prefix ((i + 1 )) (input_l)) )
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
.

Definition strange_sort_list_entail_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| ((copy_prefix (lst_size_pre) (input_l)) = input_l) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
.

Definition strange_sort_list_entail_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (sorted_full_l_2: (@list Z)) (sorted_l_2: (@list Z)) ,
  [| (lst_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l_2))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l_2)) = sorted_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l_2)) ) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| ((copy_prefix (lst_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full sorted lst_size_pre sorted_full_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
|--
  EX (sorted_full_l: (@list Z))  (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| ((0 < lst_size_pre) -> ((0 <= (0 ÷ 2 )) /\ ((0 ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((0 < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (0 ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (0 ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (0 = (Zlength ((strange_output_prefix (lst_size_pre) (0) (sorted_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 0 (strange_output_prefix (lst_size_pre) (0) (sorted_l)) )
  **  (IntArray.undef_seg data 0 lst_size_pre )
.

Definition strange_sort_list_entail_wit_5_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l_2: (@list Z)) (sorted_l_2: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l_2))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l_2)) = sorted_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l_2)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l_2))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth (i ÷ 2 ) sorted_full_l_2 0))
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_full_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l_2)) )
|--
  EX (sorted_full_l: (@list Z))  (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (((i + 1 ) < lst_size_pre) -> ((0 <= ((i + 1 ) ÷ 2 )) /\ (((i + 1 ) ÷ 2 ) < lst_size_pre))) |] 
  &&  [| (((i + 1 ) < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - ((i + 1 ) ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - ((i + 1 ) ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| ((i + 1 ) = (Zlength ((strange_output_prefix (lst_size_pre) ((i + 1 )) (sorted_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 (i + 1 ) (strange_output_prefix (lst_size_pre) ((i + 1 )) (sorted_l)) )
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
.

Definition strange_sort_list_entail_wit_5_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l_2: (@list Z)) (sorted_l_2: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l_2))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l_2)) = sorted_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l_2)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l_2))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth ((lst_size_pre - 1 ) - (i ÷ 2 ) ) sorted_full_l_2 0))
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_full_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l_2)) )
|--
  EX (sorted_full_l: (@list Z))  (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (((i + 1 ) < lst_size_pre) -> ((0 <= ((i + 1 ) ÷ 2 )) /\ (((i + 1 ) ÷ 2 ) < lst_size_pre))) |] 
  &&  [| (((i + 1 ) < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - ((i + 1 ) ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - ((i + 1 ) ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| ((i + 1 ) = (Zlength ((strange_output_prefix (lst_size_pre) ((i + 1 )) (sorted_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 (i + 1 ) (strange_output_prefix (lst_size_pre) ((i + 1 )) (sorted_l)) )
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
.

Definition strange_sort_list_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data_2: Z) (out: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data_2 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
|--
  EX (output_l: (@list Z))  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (lst_size_pre = (Zlength (output_l))) |] 
  &&  [| (problem_70_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full data lst_size_pre output_l )
.

Definition strange_sort_list_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition strange_sort_list_partial_solve_wit_2_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
.

Definition strange_sort_list_partial_solve_wit_2_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition strange_sort_list_partial_solve_wit_2 := strange_sort_list_partial_solve_wit_2_pure -> strange_sort_list_partial_solve_wit_2_aux.

Definition strange_sort_list_partial_solve_wit_3_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  ((( &( "sorted" ) )) # Ptr  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
.

Definition strange_sort_list_partial_solve_wit_3_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |]
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition strange_sort_list_partial_solve_wit_3 := strange_sort_list_partial_solve_wit_3_pure -> strange_sort_list_partial_solve_wit_3_aux.

Definition strange_sort_list_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((sorted + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (copy_prefix (i) (input_l)) )
.

Definition strange_sort_list_partial_solve_wit_6_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| ((copy_prefix (lst_size_pre) (input_l)) = input_l) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
|--
  [| (sorted <> 0) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
.

Definition strange_sort_list_partial_solve_wit_6_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| ((copy_prefix (lst_size_pre) (input_l)) = input_l) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
|--
  [| (sorted <> 0) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_70_pre_z input_l ) |] 
  &&  [| ((copy_prefix (lst_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_full data lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_6 := strange_sort_list_partial_solve_wit_6_pure -> strange_sort_list_partial_solve_wit_6_aux.

Definition strange_sort_list_partial_solve_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (((sorted + ((i ÷ 2 ) * sizeof(INT) ) )) # Int  |-> (Znth (i ÷ 2 ) sorted_full_l 0))
  **  (IntArray.missing_i sorted (i ÷ 2 ) 0 lst_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
.

Definition strange_sort_list_partial_solve_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (((sorted + (((lst_size_pre - 1 ) - (i ÷ 2 ) ) * sizeof(INT) ) )) # Int  |-> (Znth ((lst_size_pre - 1 ) - (i ÷ 2 ) ) sorted_full_l 0))
  **  (IntArray.missing_i sorted ((lst_size_pre - 1 ) - (i ÷ 2 ) ) 0 lst_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
.

Definition strange_sort_list_partial_solve_wit_11_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |]
.

Definition strange_sort_list_partial_solve_wit_11_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
  **  (IntArray.undef_seg data i lst_size_pre )
|--
  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (sorted <> 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_70_spec_z input_l (strange_output (lst_size_pre) (sorted_l)) ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= (i ÷ 2 )) /\ ((i ÷ 2 ) < lst_size_pre))) |] 
  &&  [| ((i < lst_size_pre) -> ((0 <= ((lst_size_pre - 1 ) - (i ÷ 2 ) )) /\ (((lst_size_pre - 1 ) - (i ÷ 2 ) ) < lst_size_pre))) |] 
  &&  [| (i = (Zlength ((strange_output_prefix (lst_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg data 0 i (strange_output_prefix (lst_size_pre) (i) (sorted_l)) )
.

Definition strange_sort_list_partial_solve_wit_11 := strange_sort_list_partial_solve_wit_11_pure -> strange_sort_list_partial_solve_wit_11_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_strange_sort_list_safety_wit_1 : strange_sort_list_safety_wit_1.
Axiom proof_of_strange_sort_list_safety_wit_2 : strange_sort_list_safety_wit_2.
Axiom proof_of_strange_sort_list_safety_wit_3 : strange_sort_list_safety_wit_3.
Axiom proof_of_strange_sort_list_safety_wit_4 : strange_sort_list_safety_wit_4.
Axiom proof_of_strange_sort_list_safety_wit_5 : strange_sort_list_safety_wit_5.
Axiom proof_of_strange_sort_list_safety_wit_6 : strange_sort_list_safety_wit_6.
Axiom proof_of_strange_sort_list_safety_wit_7 : strange_sort_list_safety_wit_7.
Axiom proof_of_strange_sort_list_safety_wit_8 : strange_sort_list_safety_wit_8.
Axiom proof_of_strange_sort_list_safety_wit_9 : strange_sort_list_safety_wit_9.
Axiom proof_of_strange_sort_list_safety_wit_10 : strange_sort_list_safety_wit_10.
Axiom proof_of_strange_sort_list_safety_wit_11 : strange_sort_list_safety_wit_11.
Axiom proof_of_strange_sort_list_safety_wit_12 : strange_sort_list_safety_wit_12.
Axiom proof_of_strange_sort_list_safety_wit_13 : strange_sort_list_safety_wit_13.
Axiom proof_of_strange_sort_list_safety_wit_14 : strange_sort_list_safety_wit_14.
Axiom proof_of_strange_sort_list_safety_wit_15 : strange_sort_list_safety_wit_15.
Axiom proof_of_strange_sort_list_safety_wit_16 : strange_sort_list_safety_wit_16.
Axiom proof_of_strange_sort_list_entail_wit_1 : strange_sort_list_entail_wit_1.
Axiom proof_of_strange_sort_list_entail_wit_2 : strange_sort_list_entail_wit_2.
Axiom proof_of_strange_sort_list_entail_wit_3 : strange_sort_list_entail_wit_3.
Axiom proof_of_strange_sort_list_entail_wit_4 : strange_sort_list_entail_wit_4.
Axiom proof_of_strange_sort_list_entail_wit_5_1 : strange_sort_list_entail_wit_5_1.
Axiom proof_of_strange_sort_list_entail_wit_5_2 : strange_sort_list_entail_wit_5_2.
Axiom proof_of_strange_sort_list_return_wit_1 : strange_sort_list_return_wit_1.
Axiom proof_of_strange_sort_list_partial_solve_wit_1 : strange_sort_list_partial_solve_wit_1.
Axiom proof_of_strange_sort_list_partial_solve_wit_2_pure : strange_sort_list_partial_solve_wit_2_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_2 : strange_sort_list_partial_solve_wit_2.
Axiom proof_of_strange_sort_list_partial_solve_wit_3_pure : strange_sort_list_partial_solve_wit_3_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_3 : strange_sort_list_partial_solve_wit_3.
Axiom proof_of_strange_sort_list_partial_solve_wit_4 : strange_sort_list_partial_solve_wit_4.
Axiom proof_of_strange_sort_list_partial_solve_wit_5 : strange_sort_list_partial_solve_wit_5.
Axiom proof_of_strange_sort_list_partial_solve_wit_6_pure : strange_sort_list_partial_solve_wit_6_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_6 : strange_sort_list_partial_solve_wit_6.
Axiom proof_of_strange_sort_list_partial_solve_wit_7 : strange_sort_list_partial_solve_wit_7.
Axiom proof_of_strange_sort_list_partial_solve_wit_8 : strange_sort_list_partial_solve_wit_8.
Axiom proof_of_strange_sort_list_partial_solve_wit_9 : strange_sort_list_partial_solve_wit_9.
Axiom proof_of_strange_sort_list_partial_solve_wit_10 : strange_sort_list_partial_solve_wit_10.
Axiom proof_of_strange_sort_list_partial_solve_wit_11_pure : strange_sort_list_partial_solve_wit_11_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_11 : strange_sort_list_partial_solve_wit_11.

End VC_Correct.
