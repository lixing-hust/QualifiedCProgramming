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
Require Import coins_146.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function specialFilter -----*)

Definition specialFilter_safety_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition specialFilter_safety_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition specialFilter_safety_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition specialFilter_safety_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (((Znth i input_l 0) <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition specialFilter_safety_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition specialFilter_safety_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition specialFilter_safety_wit_7 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| (first >= 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((first <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition specialFilter_safety_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| (first >= 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition specialFilter_safety_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((first <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition specialFilter_safety_wit_10 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition specialFilter_safety_wit_11 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition specialFilter_safety_wit_12 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| ((first % ( 2 ) ) = 1) |] 
  &&  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((last <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition specialFilter_safety_wit_13 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| ((first % ( 2 ) ) = 1) |] 
  &&  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition specialFilter_safety_wit_14 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| ((first % ( 2 ) ) = 1) |] 
  &&  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition specialFilter_safety_wit_15 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (first_addr_v: Z) (last_addr_v: Z) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (special_number_c (Znth (i) (input_l) (0)) ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "first" ) )) # Int  |-> first_addr_v)
  **  ((( &( "last" ) )) # Int  |-> last_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((num + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + 1 )) |]
.

Definition specialFilter_safety_wit_16 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (first_addr_v: Z) (last_addr_v: Z) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (special_number_c (Znth (i) (input_l) (0)) ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "first" ) )) # Int  |-> first_addr_v)
  **  ((( &( "last" ) )) # Int  |-> last_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition specialFilter_safety_wit_17 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition specialFilter_entail_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (special_filter_prefix 0 input_l 0 ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= ((Znth i input_l 0) % ( 10 ) )) |] 
  &&  [| (((Znth i input_l 0) % ( 10 ) ) <= 9) |] 
  &&  [| (((Znth i input_l 0) % ( 10 ) ) = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) (Znth i input_l 0) ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| (first >= 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) (first ÷ 10 ) ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| ((last % ( 2 ) ) = 1) |] 
  &&  [| ((first % ( 2 ) ) = 1) |] 
  &&  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (special_number_c (Znth (i) (input_l) (0)) ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_5_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (special_number_c (Znth (i) (input_l) (0)) ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l (num + 1 ) ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_5_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| ((first % ( 2 ) ) <> 1) |] 
  &&  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_5_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (first: Z) (last: Z) (num: Z) (i: Z) ,
  [| ((last % ( 2 ) ) <> 1) |] 
  &&  [| ((first % ( 2 ) ) = 1) |] 
  &&  [| (first < 10) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |] 
  &&  [| (10 < (Znth (i) (input_l) (0))) |] 
  &&  [| (0 <= last) |] 
  &&  [| (last <= 9) |] 
  &&  [| (last = ((Znth (i) (input_l) (0)) % ( 10 ) )) |] 
  &&  [| (first_digit_state (Znth (i) (input_l) (0)) first ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_6_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_6_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_7 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nums_size_pre) |] 
  &&  [| (special_filter_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_return_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| (i >= nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (problem_146_spec_z input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_partial_solve_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
.

Definition specialFilter_partial_solve_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((Znth i input_l 0) > 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
.

Definition specialFilter_partial_solve_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((Znth i input_l 0) > 10) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_146_pre_z input_l ) |] 
  &&  [| (special_filter_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (special_filter_prefix i input_l num ) |]
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_specialFilter_safety_wit_1 : specialFilter_safety_wit_1.
Axiom proof_of_specialFilter_safety_wit_2 : specialFilter_safety_wit_2.
Axiom proof_of_specialFilter_safety_wit_3 : specialFilter_safety_wit_3.
Axiom proof_of_specialFilter_safety_wit_4 : specialFilter_safety_wit_4.
Axiom proof_of_specialFilter_safety_wit_5 : specialFilter_safety_wit_5.
Axiom proof_of_specialFilter_safety_wit_6 : specialFilter_safety_wit_6.
Axiom proof_of_specialFilter_safety_wit_7 : specialFilter_safety_wit_7.
Axiom proof_of_specialFilter_safety_wit_8 : specialFilter_safety_wit_8.
Axiom proof_of_specialFilter_safety_wit_9 : specialFilter_safety_wit_9.
Axiom proof_of_specialFilter_safety_wit_10 : specialFilter_safety_wit_10.
Axiom proof_of_specialFilter_safety_wit_11 : specialFilter_safety_wit_11.
Axiom proof_of_specialFilter_safety_wit_12 : specialFilter_safety_wit_12.
Axiom proof_of_specialFilter_safety_wit_13 : specialFilter_safety_wit_13.
Axiom proof_of_specialFilter_safety_wit_14 : specialFilter_safety_wit_14.
Axiom proof_of_specialFilter_safety_wit_15 : specialFilter_safety_wit_15.
Axiom proof_of_specialFilter_safety_wit_16 : specialFilter_safety_wit_16.
Axiom proof_of_specialFilter_safety_wit_17 : specialFilter_safety_wit_17.
Axiom proof_of_specialFilter_entail_wit_1 : specialFilter_entail_wit_1.
Axiom proof_of_specialFilter_entail_wit_2 : specialFilter_entail_wit_2.
Axiom proof_of_specialFilter_entail_wit_3 : specialFilter_entail_wit_3.
Axiom proof_of_specialFilter_entail_wit_4 : specialFilter_entail_wit_4.
Axiom proof_of_specialFilter_entail_wit_5_1 : specialFilter_entail_wit_5_1.
Axiom proof_of_specialFilter_entail_wit_5_2 : specialFilter_entail_wit_5_2.
Axiom proof_of_specialFilter_entail_wit_5_3 : specialFilter_entail_wit_5_3.
Axiom proof_of_specialFilter_entail_wit_6_1 : specialFilter_entail_wit_6_1.
Axiom proof_of_specialFilter_entail_wit_6_2 : specialFilter_entail_wit_6_2.
Axiom proof_of_specialFilter_entail_wit_7 : specialFilter_entail_wit_7.
Axiom proof_of_specialFilter_return_wit_1 : specialFilter_return_wit_1.
Axiom proof_of_specialFilter_partial_solve_wit_1 : specialFilter_partial_solve_wit_1.
Axiom proof_of_specialFilter_partial_solve_wit_2 : specialFilter_partial_solve_wit_2.
Axiom proof_of_specialFilter_partial_solve_wit_3 : specialFilter_partial_solve_wit_3.

End VC_Correct.
