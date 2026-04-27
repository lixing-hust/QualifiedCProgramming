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
Require Import coins_33.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function sort_third -----*)

Definition sort_third_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((( &( "third_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (((l_size_pre + 2 ) <> (INT_MIN)) \/ (3 <> (-1))) |] 
  &&  [| (3 <> 0) |]
.

Definition sort_third_safety_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((( &( "third_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| ((l_size_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (l_size_pre + 2 )) |]
.

Definition sort_third_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((( &( "third_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition sort_third_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((( &( "third_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition sort_third_safety_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 l_size_pre )
  **  ((( &( "third" ) )) # Ptr  |-> retval_3)
  **  ((( &( "third_size" ) )) # Int  |-> ((l_size_pre + 2 ) ÷ 3 ))
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_third_safety_wit_6 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
|--
  [| ((i * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 3 )) |]
.

Definition sort_third_safety_wit_7 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition sort_third_safety_wit_8 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  (((third + (i * sizeof(INT) ) )) # Int  |-> (Znth (i * 3 ) input_l 0))
  **  (IntArray.undef_seg third (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sort_third_safety_wit_9 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
|--
  [| ((i * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 3 )) |]
.

Definition sort_third_safety_wit_10 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition sort_third_safety_wit_11 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (third: Z) (third_size: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (i = third_size) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 third_size (third_values_prefix (third_size) (input_l)) )
  **  (IntArray.undef_seg third third_size l_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sort_third_safety_wit_12 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (sorted_third_l: (@list Z)) (sorted_full_l: (@list Z)) (out: Z) (data: Z) (third: Z) (third_size: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (i = third_size) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_third_safety_wit_13 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (sorted_third_l: (@list Z)) (sorted_full_l: (@list Z)) (out: Z) (data: Z) (third: Z) (third_size: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (i = third_size) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_third_safety_wit_14 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| ((i <> (INT_MIN)) \/ (3 <> (-1))) |] 
  &&  [| (3 <> 0) |]
.

Definition sort_third_safety_wit_15 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition sort_third_safety_wit_16 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sort_third_safety_wit_17 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth j sorted_full_l 0))
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sort_third_safety_wit_18 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth j sorted_full_l 0))
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sort_third_safety_wit_19 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) <> 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sort_third_safety_wit_20 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth j sorted_full_l 0))
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sort_third_entail_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  (IntArray.undef_full retval_3 l_size_pre )
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (((l_size_pre + 2 ) ÷ 3 ) = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= ((l_size_pre + 2 ) ÷ 3 )) |] 
  &&  [| (((l_size_pre + 2 ) ÷ 3 ) <= l_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= ((l_size_pre + 2 ) ÷ 3 )) |] 
  &&  [| ((3 * 0 ) <= (l_size_pre + 2 )) |] 
  &&  [| (0 = (Zlength ((third_values_prefix (0) (input_l))))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  (IntArray.seg retval_3 0 0 (third_values_prefix (0) (input_l)) )
  **  (IntArray.undef_seg retval_3 0 l_size_pre )
.

Definition sort_third_entail_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  (((third + (i * sizeof(INT) ) )) # Int  |-> (Znth (i * 3 ) input_l 0))
  **  (IntArray.undef_seg third (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= third_size) |] 
  &&  [| ((3 * (i + 1 ) ) <= (l_size_pre + 2 )) |] 
  &&  [| ((i + 1 ) = (Zlength ((third_values_prefix ((i + 1 )) (input_l))))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 (i + 1 ) (third_values_prefix ((i + 1 )) (input_l)) )
  **  (IntArray.undef_seg third (i + 1 ) l_size_pre )
.

Definition sort_third_entail_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i * 3 ) >= l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (i = third_size) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 third_size (third_values_prefix (third_size) (input_l)) )
  **  (IntArray.undef_seg third third_size l_size_pre )
.

Definition sort_third_entail_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (third: Z) (third_size: Z) (i: Z) (sorted_full_l_2: (@list Z)) (sorted_l: (@list Z)) ,
  [| (third_size = (Zlength (sorted_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l_2))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l_2)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_l ) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (i = third_size) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |]
  &&  (IntArray.full third l_size_pre sorted_full_l_2 )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
|--
  EX (sorted_full_l: (@list Z))  (sorted_third_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (i = third_size) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
.

Definition sort_third_entail_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (sorted_third_l_2: (@list Z)) (sorted_full_l_2: (@list Z)) (out: Z) (data: Z) (third: Z) (third_size: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l_2))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l_2))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l_2)) = sorted_third_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l_2 ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l_2 ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (i = third_size) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l_2 )
|--
  EX (sorted_full_l: (@list Z))  (sorted_third_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (third_count (0))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 0 (sort_third_output_prefix (0) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data 0 l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
.

Definition sort_third_entail_wit_6_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l_2: (@list Z)) (sorted_third_l_2: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l_2))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l_2))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l_2)) = sorted_third_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l_2 ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l_2 ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth j sorted_full_l_2 0))
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l_2 )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l_2)) )
|--
  EX (sorted_full_l: (@list Z))  (sorted_third_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= (i + 1 )) |] 
  &&  [| ((j + 1 ) = (third_count ((i + 1 )))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 (i + 1 ) (sort_third_output_prefix ((i + 1 )) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
.

Definition sort_third_entail_wit_6_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l_2: (@list Z)) (sorted_third_l_2: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) <> 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l_2))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l_2))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l_2)) = sorted_third_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l_2 ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l_2 ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l_2)) )
  **  (IntArray.full third l_size_pre sorted_full_l_2 )
|--
  EX (sorted_full_l: (@list Z))  (sorted_third_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| (j = (third_count ((i + 1 )))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 (i + 1 ) (sort_third_output_prefix ((i + 1 )) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
.

Definition sort_third_return_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data_2: Z) (out: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data_2 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = l_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_33_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition sort_third_partial_solve_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition sort_third_partial_solve_wit_2_pure := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (l_size_pre >= 0) |] 
  &&  [| (l_size_pre < INT_MAX) |]
.

Definition sort_third_partial_solve_wit_2_aux := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (l_size_pre >= 0) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition sort_third_partial_solve_wit_2 := sort_third_partial_solve_wit_2_pure -> sort_third_partial_solve_wit_2_aux.

Definition sort_third_partial_solve_wit_3_pure := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  ((( &( "third" ) )) # Ptr  |->_)
  **  ((( &( "third_size" ) )) # Int  |-> ((l_size_pre + 2 ) ÷ 3 ))
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (l_size_pre >= 0) |] 
  &&  [| (l_size_pre < INT_MAX) |]
.

Definition sort_third_partial_solve_wit_3_aux := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (l_size_pre >= 0) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_33_pre_z input_l ) |]
  &&  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition sort_third_partial_solve_wit_3 := sort_third_partial_solve_wit_3_pure -> sort_third_partial_solve_wit_3_aux.

Definition sort_third_partial_solve_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
|--
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  (((l_pre + ((i * 3 ) * sizeof(INT) ) )) # Int  |-> (Znth (i * 3 ) input_l 0))
  **  (IntArray.missing_i l_pre (i * 3 ) 0 l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
.

Definition sort_third_partial_solve_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
  **  (IntArray.undef_seg third i l_size_pre )
|--
  [| ((i * 3 ) < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= third_size) |] 
  &&  [| ((3 * i ) <= (l_size_pre + 2 )) |] 
  &&  [| (i = (Zlength ((third_values_prefix (i) (input_l))))) |]
  &&  (((third + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg third (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 i (third_values_prefix (i) (input_l)) )
.

Definition sort_third_partial_solve_wit_6_pure := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (third: Z) (third_size: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (i = third_size) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 third_size (third_values_prefix (third_size) (input_l)) )
  **  (IntArray.undef_seg third third_size l_size_pre )
|--
  [| (third <> 0) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
.

Definition sort_third_partial_solve_wit_6_aux := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (third: Z) (third_size: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (i = third_size) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
  **  (IntArray.seg third 0 third_size (third_values_prefix (third_size) (input_l)) )
  **  (IntArray.undef_seg third third_size l_size_pre )
|--
  [| (third <> 0) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= third_size) |] 
  &&  [| (third_size <= l_size_pre) |] 
  &&  [| (i = third_size) |] 
  &&  [| (third_size = (Zlength ((third_values_prefix (third_size) (input_l))))) |]
  &&  (IntArray.seg third 0 third_size (third_values_prefix (third_size) (input_l)) )
  **  (IntArray.undef_seg third third_size l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.undef_full data l_size_pre )
.

Definition sort_third_partial_solve_wit_6 := sort_third_partial_solve_wit_6_pure -> sort_third_partial_solve_wit_6_aux.

Definition sort_third_partial_solve_wit_7 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((third + (j * sizeof(INT) ) )) # Int  |-> (Znth j sorted_full_l 0))
  **  (IntArray.missing_i third j 0 l_size_pre sorted_full_l )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
.

Definition sort_third_partial_solve_wit_8 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (IntArray.full third l_size_pre sorted_full_l )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
|--
  [| ((i % ( 3 ) ) = 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
.

Definition sort_third_partial_solve_wit_9 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) <> 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| ((i % ( 3 ) ) <> 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
.

Definition sort_third_partial_solve_wit_10 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| ((i % ( 3 ) ) <> 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| ((i % ( 3 ) ) <> 0) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.full third l_size_pre sorted_full_l )
.

Definition sort_third_partial_solve_wit_11_pure := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "third" ) )) # Ptr  |-> third)
  **  ((( &( "third_size" ) )) # Int  |-> third_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |]
.

Definition sort_third_partial_solve_wit_11_aux := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) (sorted_full_l: (@list Z)) (sorted_third_l: (@list Z)) (third_size: Z) (third: Z) (data: Z) (out: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full third l_size_pre sorted_full_l )
|--
  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| (i >= l_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (third <> 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < (INT_MAX - 2 )) |] 
  &&  [| (l_size_pre = (Zlength (input_l))) |] 
  &&  [| (third_size = (third_count (l_size_pre))) |] 
  &&  [| (third_size = (Zlength (sorted_third_l))) |] 
  &&  [| (l_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (third_size) (sorted_full_l)) = sorted_third_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_third_l ) |] 
  &&  [| (Permutation (third_values_prefix (third_size) (input_l)) sorted_third_l ) |] 
  &&  [| (problem_33_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (j = (third_count (i))) |]
  &&  (IntArray.full third l_size_pre sorted_full_l )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data 0 i (sort_third_output_prefix (i) (input_l) (sorted_third_l)) )
.

Definition sort_third_partial_solve_wit_11 := sort_third_partial_solve_wit_11_pure -> sort_third_partial_solve_wit_11_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_sort_third_safety_wit_1 : sort_third_safety_wit_1.
Axiom proof_of_sort_third_safety_wit_2 : sort_third_safety_wit_2.
Axiom proof_of_sort_third_safety_wit_3 : sort_third_safety_wit_3.
Axiom proof_of_sort_third_safety_wit_4 : sort_third_safety_wit_4.
Axiom proof_of_sort_third_safety_wit_5 : sort_third_safety_wit_5.
Axiom proof_of_sort_third_safety_wit_6 : sort_third_safety_wit_6.
Axiom proof_of_sort_third_safety_wit_7 : sort_third_safety_wit_7.
Axiom proof_of_sort_third_safety_wit_8 : sort_third_safety_wit_8.
Axiom proof_of_sort_third_safety_wit_9 : sort_third_safety_wit_9.
Axiom proof_of_sort_third_safety_wit_10 : sort_third_safety_wit_10.
Axiom proof_of_sort_third_safety_wit_11 : sort_third_safety_wit_11.
Axiom proof_of_sort_third_safety_wit_12 : sort_third_safety_wit_12.
Axiom proof_of_sort_third_safety_wit_13 : sort_third_safety_wit_13.
Axiom proof_of_sort_third_safety_wit_14 : sort_third_safety_wit_14.
Axiom proof_of_sort_third_safety_wit_15 : sort_third_safety_wit_15.
Axiom proof_of_sort_third_safety_wit_16 : sort_third_safety_wit_16.
Axiom proof_of_sort_third_safety_wit_17 : sort_third_safety_wit_17.
Axiom proof_of_sort_third_safety_wit_18 : sort_third_safety_wit_18.
Axiom proof_of_sort_third_safety_wit_19 : sort_third_safety_wit_19.
Axiom proof_of_sort_third_safety_wit_20 : sort_third_safety_wit_20.
Axiom proof_of_sort_third_entail_wit_1 : sort_third_entail_wit_1.
Axiom proof_of_sort_third_entail_wit_2 : sort_third_entail_wit_2.
Axiom proof_of_sort_third_entail_wit_3 : sort_third_entail_wit_3.
Axiom proof_of_sort_third_entail_wit_4 : sort_third_entail_wit_4.
Axiom proof_of_sort_third_entail_wit_5 : sort_third_entail_wit_5.
Axiom proof_of_sort_third_entail_wit_6_1 : sort_third_entail_wit_6_1.
Axiom proof_of_sort_third_entail_wit_6_2 : sort_third_entail_wit_6_2.
Axiom proof_of_sort_third_return_wit_1 : sort_third_return_wit_1.
Axiom proof_of_sort_third_partial_solve_wit_1 : sort_third_partial_solve_wit_1.
Axiom proof_of_sort_third_partial_solve_wit_2_pure : sort_third_partial_solve_wit_2_pure.
Axiom proof_of_sort_third_partial_solve_wit_2 : sort_third_partial_solve_wit_2.
Axiom proof_of_sort_third_partial_solve_wit_3_pure : sort_third_partial_solve_wit_3_pure.
Axiom proof_of_sort_third_partial_solve_wit_3 : sort_third_partial_solve_wit_3.
Axiom proof_of_sort_third_partial_solve_wit_4 : sort_third_partial_solve_wit_4.
Axiom proof_of_sort_third_partial_solve_wit_5 : sort_third_partial_solve_wit_5.
Axiom proof_of_sort_third_partial_solve_wit_6_pure : sort_third_partial_solve_wit_6_pure.
Axiom proof_of_sort_third_partial_solve_wit_6 : sort_third_partial_solve_wit_6.
Axiom proof_of_sort_third_partial_solve_wit_7 : sort_third_partial_solve_wit_7.
Axiom proof_of_sort_third_partial_solve_wit_8 : sort_third_partial_solve_wit_8.
Axiom proof_of_sort_third_partial_solve_wit_9 : sort_third_partial_solve_wit_9.
Axiom proof_of_sort_third_partial_solve_wit_10 : sort_third_partial_solve_wit_10.
Axiom proof_of_sort_third_partial_solve_wit_11_pure : sort_third_partial_solve_wit_11_pure.
Axiom proof_of_sort_third_partial_solve_wit_11 : sort_third_partial_solve_wit_11.

End VC_Correct.
