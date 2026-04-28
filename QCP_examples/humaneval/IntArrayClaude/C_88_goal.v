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
Require Import coins_88.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function sort_array -----*)

Definition sort_array_safety_wit_1 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 array_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_array_safety_wit_2 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 array_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_array_safety_wit_3 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (array_size_pre <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 array_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_array_safety_wit_4 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < array_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= array_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) array_size_pre )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
  **  (IntArray.seg data 0 i (copy_prefix (i) (input_l)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sort_array_safety_wit_5 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| ((((Znth 0 input_l 0) + (Znth (array_size_pre - 1 ) input_l 0) ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition sort_array_safety_wit_6 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| (((Znth 0 input_l 0) + (Znth (array_size_pre - 1 ) input_l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 0 input_l 0) + (Znth (array_size_pre - 1 ) input_l 0) )) |]
.

Definition sort_array_safety_wit_7 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| ((array_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (array_size_pre - 1 )) |]
.

Definition sort_array_safety_wit_8 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_array_safety_wit_9 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sort_array_safety_wit_10 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition sort_array_safety_wit_11 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_array_safety_wit_12 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| ((((Znth 0 input_l 0) + (Znth (array_size_pre - 1 ) input_l 0) ) % ( 2 ) ) = 0) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_array_safety_wit_13 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
  **  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
|--
  [| ((array_size_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition sort_array_safety_wit_14 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
  **  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition sort_array_safety_wit_15 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
|--
  [| (((array_size_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((array_size_pre - 1 ) - i )) |]
.

Definition sort_array_safety_wit_16 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
|--
  [| ((array_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (array_size_pre - 1 )) |]
.

Definition sort_array_safety_wit_17 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sort_array_safety_wit_18 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (replace_Znth (i) ((Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l)) 0)) ((reverse_loop (array_size_pre) (i) (sorted_l)))) )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
|--
  [| (((array_size_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((array_size_pre - 1 ) - i )) |]
.

Definition sort_array_safety_wit_19 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (replace_Znth (i) ((Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l)) 0)) ((reverse_loop (array_size_pre) (i) (sorted_l)))) )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
|--
  [| ((array_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (array_size_pre - 1 )) |]
.

Definition sort_array_safety_wit_20 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (replace_Znth (i) ((Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l)) 0)) ((reverse_loop (array_size_pre) (i) (sorted_l)))) )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sort_array_safety_wit_21 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (replace_Znth (((array_size_pre - 1 ) - i )) ((Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0)) ((replace_Znth (i) ((Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l)) 0)) ((reverse_loop (array_size_pre) (i) (sorted_l)))))) )
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sort_array_entail_wit_1 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (array_size_pre <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  (IntArray.undef_full retval_2 array_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
|--
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (0 = (Zlength ((copy_prefix (0) (input_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg retval_2 0 0 (copy_prefix (0) (input_l)) )
  **  (IntArray.undef_seg retval_2 0 array_size_pre )
.

Definition sort_array_entail_wit_2 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (data: Z) (out: Z) ,
  [| (i < array_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= array_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) array_size_pre )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg data 0 i (copy_prefix (i) (input_l)) )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= array_size_pre) |] 
  &&  [| ((i + 1 ) = (Zlength ((copy_prefix ((i + 1 )) (input_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg data 0 (i + 1 ) (copy_prefix ((i + 1 )) (input_l)) )
  **  (IntArray.undef_seg data (i + 1 ) array_size_pre )
.

Definition sort_array_entail_wit_3 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (data: Z) (out: Z) ,
  [| (i >= array_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= array_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg data 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg data i array_size_pre )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  (IntArray.full data array_size_pre input_l )
.

Definition sort_array_entail_wit_4 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted_l_2: (@list Z)) ,
  [| ((((Znth 0 input_l 0) + (Znth (array_size_pre - 1 ) input_l 0) ) % ( 2 ) ) = 0) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l_2 )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l_2)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  EX (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((0 < (array_size_pre ÷ 2 )) -> ((0 <= 0) /\ (0 < array_size_pre))) |] 
  &&  [| ((0 < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - 0 )) /\ (((array_size_pre - 1 ) - 0 ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (0) (sorted_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (0) (sorted_l)) )
.

Definition sort_array_entail_wit_5 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l_2: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l_2)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l_2))))) |]
  &&  (IntArray.full data array_size_pre (replace_Znth (((array_size_pre - 1 ) - i )) ((Znth i (reverse_loop (array_size_pre) (i) (sorted_l_2)) 0)) ((replace_Znth (i) ((Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l_2)) 0)) ((reverse_loop (array_size_pre) (i) (sorted_l_2)))))) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  EX (sorted_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (array_size_pre ÷ 2 )) |] 
  &&  [| (((i + 1 ) < (array_size_pre ÷ 2 )) -> ((0 <= (i + 1 )) /\ ((i + 1 ) < array_size_pre))) |] 
  &&  [| (((i + 1 ) < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - (i + 1 ) )) /\ (((array_size_pre - 1 ) - (i + 1 ) ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) ((i + 1 )) (sorted_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) ((i + 1 )) (sorted_l)) )
.

Definition sort_array_return_wit_1 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data_2: Z) (out: Z) ,
  [| (i >= (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full data_2 array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
|--
  EX (output_l: (@list Z))  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (array_size_pre = (Zlength (output_l))) |] 
  &&  [| (problem_88_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre output_l )
.

Definition sort_array_return_wit_2 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (out: Z) (data_2: Z) (sorted_l: (@list Z)) ,
  [| ((((Znth 0 input_l 0) + (Znth (array_size_pre - 1 ) input_l 0) ) % ( 2 ) ) <> 0) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data_2 array_size_pre sorted_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  EX (output_l: (@list Z))  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (array_size_pre = (Zlength (output_l))) |] 
  &&  [| (problem_88_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre output_l )
.

Definition sort_array_return_wit_3 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (array_size_pre = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  (IntArray.undef_full retval_2 array_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
|--
  EX (output_l: (@list Z))  (data: Z) ,
  [| (retval <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (array_size_pre = (Zlength (output_l))) |] 
  &&  [| (problem_88_spec_z input_l output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre output_l )
.

Definition sort_array_partial_solve_wit_1 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
|--
  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
.

Definition sort_array_partial_solve_wit_2_pure := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
|--
  [| (array_size_pre >= 0) |] 
  &&  [| (array_size_pre < INT_MAX) |]
.

Definition sort_array_partial_solve_wit_2_aux := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
|--
  [| (array_size_pre >= 0) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full array_pre array_size_pre input_l )
.

Definition sort_array_partial_solve_wit_2 := sort_array_partial_solve_wit_2_pure -> sort_array_partial_solve_wit_2_aux.

Definition sort_array_partial_solve_wit_3 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (data: Z) (out: Z) ,
  [| (i < array_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= array_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg data 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg data i array_size_pre )
|--
  [| (i < array_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= array_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((array_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i array_pre i 0 array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg data 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg data i array_size_pre )
.

Definition sort_array_partial_solve_wit_4 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (data: Z) (out: Z) ,
  [| (i < array_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= array_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg data 0 i (copy_prefix (i) (input_l)) )
  **  (IntArray.undef_seg data i array_size_pre )
|--
  [| (i < array_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= array_size_pre) |] 
  &&  [| (i = (Zlength ((copy_prefix (i) (input_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) array_size_pre )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.seg data 0 i (copy_prefix (i) (input_l)) )
.

Definition sort_array_partial_solve_wit_5_pure := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (t_v: Z) (out: Z) (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((( &( "array_size" ) )) # Int  |-> array_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  ((( &( "i" ) )) # Int  |-> array_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_v)
  **  (IntArray.full data array_size_pre input_l )
|--
  [| (data <> 0) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (sort_array_input_range input_l ) |]
.

Definition sort_array_partial_solve_wit_5_aux := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full data array_size_pre input_l )
|--
  [| (data <> 0) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full data array_size_pre input_l )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
.

Definition sort_array_partial_solve_wit_5 := sort_array_partial_solve_wit_5_pure -> sort_array_partial_solve_wit_5_aux.

Definition sort_array_partial_solve_wit_6 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full data array_size_pre sorted_l )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (((array_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 input_l 0))
  **  (IntArray.missing_i array_pre 0 0 array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
.

Definition sort_array_partial_solve_wit_7 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted_l: (@list Z)) ,
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (((array_size_pre = 0) \/ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) <> 0)) -> (problem_88_spec_z input_l sorted_l )) |] 
  &&  [| (((0 < array_size_pre) /\ ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0)) -> (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| ((copy_prefix (array_size_pre) (input_l)) = input_l) |]
  &&  (((array_pre + ((array_size_pre - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (array_size_pre - 1 ) input_l 0))
  **  (IntArray.missing_i array_pre (array_size_pre - 1 ) 0 array_size_pre input_l )
  **  (IntArray.full data array_size_pre sorted_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
.

Definition sort_array_partial_solve_wit_8 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
  **  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
|--
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
  **  (IntArray.missing_i data i 0 array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
.

Definition sort_array_partial_solve_wit_9 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (((array_size_pre - 1 ) - i ) * sizeof(INT) ) )) # Int  |-> (Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l)) 0))
  **  (IntArray.missing_i data ((array_size_pre - 1 ) - i ) 0 array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
.

Definition sort_array_partial_solve_wit_10 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data i 0 array_size_pre (reverse_loop (array_size_pre) (i) (sorted_l)) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
.

Definition sort_array_partial_solve_wit_11 := 
forall (array_size_pre: Z) (array_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) (data: Z) (out: Z) ,
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (IntArray.full data array_size_pre (replace_Znth (i) ((Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l)) 0)) ((reverse_loop (array_size_pre) (i) (sorted_l)))) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
|--
  [| (i < (array_size_pre ÷ 2 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < array_size_pre) |] 
  &&  [| (array_size_pre < INT_MAX) |] 
  &&  [| (array_size_pre = (Zlength (input_l))) |] 
  &&  [| (array_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_88_pre_z input_l ) |] 
  &&  [| (sort_array_input_range input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (problem_88_spec_z input_l (reverse_loop (array_size_pre) ((array_size_pre ÷ 2 )) (sorted_l)) ) |] 
  &&  [| ((((Znth (0) (input_l) (0)) + (Znth ((array_size_pre - 1 )) (input_l) (0)) ) % ( 2 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (array_size_pre ÷ 2 )) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= i) /\ (i < array_size_pre))) |] 
  &&  [| ((i < (array_size_pre ÷ 2 )) -> ((0 <= ((array_size_pre - 1 ) - i )) /\ (((array_size_pre - 1 ) - i ) < array_size_pre))) |] 
  &&  [| (array_size_pre = (Zlength ((reverse_loop (array_size_pre) (i) (sorted_l))))) |]
  &&  (((data + (((array_size_pre - 1 ) - i ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data ((array_size_pre - 1 ) - i ) 0 array_size_pre (replace_Znth (i) ((Znth ((array_size_pre - 1 ) - i ) (reverse_loop (array_size_pre) (i) (sorted_l)) 0)) ((reverse_loop (array_size_pre) (i) (sorted_l)))) )
  **  (IntArray.full array_pre array_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> array_size_pre)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_sort_array_safety_wit_1 : sort_array_safety_wit_1.
Axiom proof_of_sort_array_safety_wit_2 : sort_array_safety_wit_2.
Axiom proof_of_sort_array_safety_wit_3 : sort_array_safety_wit_3.
Axiom proof_of_sort_array_safety_wit_4 : sort_array_safety_wit_4.
Axiom proof_of_sort_array_safety_wit_5 : sort_array_safety_wit_5.
Axiom proof_of_sort_array_safety_wit_6 : sort_array_safety_wit_6.
Axiom proof_of_sort_array_safety_wit_7 : sort_array_safety_wit_7.
Axiom proof_of_sort_array_safety_wit_8 : sort_array_safety_wit_8.
Axiom proof_of_sort_array_safety_wit_9 : sort_array_safety_wit_9.
Axiom proof_of_sort_array_safety_wit_10 : sort_array_safety_wit_10.
Axiom proof_of_sort_array_safety_wit_11 : sort_array_safety_wit_11.
Axiom proof_of_sort_array_safety_wit_12 : sort_array_safety_wit_12.
Axiom proof_of_sort_array_safety_wit_13 : sort_array_safety_wit_13.
Axiom proof_of_sort_array_safety_wit_14 : sort_array_safety_wit_14.
Axiom proof_of_sort_array_safety_wit_15 : sort_array_safety_wit_15.
Axiom proof_of_sort_array_safety_wit_16 : sort_array_safety_wit_16.
Axiom proof_of_sort_array_safety_wit_17 : sort_array_safety_wit_17.
Axiom proof_of_sort_array_safety_wit_18 : sort_array_safety_wit_18.
Axiom proof_of_sort_array_safety_wit_19 : sort_array_safety_wit_19.
Axiom proof_of_sort_array_safety_wit_20 : sort_array_safety_wit_20.
Axiom proof_of_sort_array_safety_wit_21 : sort_array_safety_wit_21.
Axiom proof_of_sort_array_entail_wit_1 : sort_array_entail_wit_1.
Axiom proof_of_sort_array_entail_wit_2 : sort_array_entail_wit_2.
Axiom proof_of_sort_array_entail_wit_3 : sort_array_entail_wit_3.
Axiom proof_of_sort_array_entail_wit_4 : sort_array_entail_wit_4.
Axiom proof_of_sort_array_entail_wit_5 : sort_array_entail_wit_5.
Axiom proof_of_sort_array_return_wit_1 : sort_array_return_wit_1.
Axiom proof_of_sort_array_return_wit_2 : sort_array_return_wit_2.
Axiom proof_of_sort_array_return_wit_3 : sort_array_return_wit_3.
Axiom proof_of_sort_array_partial_solve_wit_1 : sort_array_partial_solve_wit_1.
Axiom proof_of_sort_array_partial_solve_wit_2_pure : sort_array_partial_solve_wit_2_pure.
Axiom proof_of_sort_array_partial_solve_wit_2 : sort_array_partial_solve_wit_2.
Axiom proof_of_sort_array_partial_solve_wit_3 : sort_array_partial_solve_wit_3.
Axiom proof_of_sort_array_partial_solve_wit_4 : sort_array_partial_solve_wit_4.
Axiom proof_of_sort_array_partial_solve_wit_5_pure : sort_array_partial_solve_wit_5_pure.
Axiom proof_of_sort_array_partial_solve_wit_5 : sort_array_partial_solve_wit_5.
Axiom proof_of_sort_array_partial_solve_wit_6 : sort_array_partial_solve_wit_6.
Axiom proof_of_sort_array_partial_solve_wit_7 : sort_array_partial_solve_wit_7.
Axiom proof_of_sort_array_partial_solve_wit_8 : sort_array_partial_solve_wit_8.
Axiom proof_of_sort_array_partial_solve_wit_9 : sort_array_partial_solve_wit_9.
Axiom proof_of_sort_array_partial_solve_wit_10 : sort_array_partial_solve_wit_10.
Axiom proof_of_sort_array_partial_solve_wit_11 : sort_array_partial_solve_wit_11.

End VC_Correct.
