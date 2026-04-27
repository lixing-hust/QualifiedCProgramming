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
Require Import coins_114.
Local Open Scope sac.
Require Import long_array_strategy_goal.
Require Import long_array_strategy_proof.

(*----- Function minSubArraySum -----*)

Definition minSubArraySum_safety_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) ,
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  ((( &( "min" ) )) # Int64  |->_)
  **  ((( &( "current" ) )) # Int64  |->_)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition minSubArraySum_safety_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) ,
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "min" ) )) # Int64  |->_)
  **  ((( &( "current" ) )) # Int64  |-> (Znth 0 nums_l 0))
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition minSubArraySum_safety_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) ,
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (LongArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "min" ) )) # Int64  |-> (Znth 0 nums_l 0))
  **  ((( &( "current" ) )) # Int64  |-> (Znth 0 nums_l 0))
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition minSubArraySum_safety_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int64  |-> current)
  **  ((( &( "min" ) )) # Int64  |-> min)
  **  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition minSubArraySum_safety_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| (current < 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int64  |-> current)
  **  ((( &( "min" ) )) # Int64  |-> min)
|--
  [| ((current + (Znth i nums_l 0) ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (current + (Znth i nums_l 0) )) |]
.

Definition minSubArraySum_safety_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((current + (Znth i nums_l 0) ) >= min) |] 
  &&  [| (current < 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int64  |-> (current + (Znth i nums_l 0) ))
  **  ((( &( "min" ) )) # Int64  |-> min)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition minSubArraySum_safety_wit_7 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((Znth i nums_l 0) >= min) |] 
  &&  [| (current >= 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int64  |-> (Znth i nums_l 0))
  **  ((( &( "min" ) )) # Int64  |-> min)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition minSubArraySum_safety_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((Znth i nums_l 0) < min) |] 
  &&  [| (current >= 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int64  |-> (Znth i nums_l 0))
  **  ((( &( "min" ) )) # Int64  |-> (Znth i nums_l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition minSubArraySum_safety_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((current + (Znth i nums_l 0) ) < min) |] 
  &&  [| (current < 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int64  |-> (current + (Znth i nums_l 0) ))
  **  ((( &( "min" ) )) # Int64  |-> (current + (Znth i nums_l 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition minSubArraySum_entail_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) ,
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| ((Znth 0 nums_l 0) = (min_suffix_prefix (1) (nums_l))) |] 
  &&  [| ((Znth 0 nums_l 0) = (min_subarray_prefix (1) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
.

Definition minSubArraySum_entail_wit_2_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((current + (Znth i nums_l 0) ) < min) |] 
  &&  [| (current < 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nums_size_pre) |] 
  &&  [| ((current + (Znth i nums_l 0) ) = (min_suffix_prefix ((i + 1 )) (nums_l))) |] 
  &&  [| ((current + (Znth i nums_l 0) ) = (min_subarray_prefix ((i + 1 )) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
.

Definition minSubArraySum_entail_wit_2_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((Znth i nums_l 0) < min) |] 
  &&  [| (current >= 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nums_size_pre) |] 
  &&  [| ((Znth i nums_l 0) = (min_suffix_prefix ((i + 1 )) (nums_l))) |] 
  &&  [| ((Znth i nums_l 0) = (min_subarray_prefix ((i + 1 )) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
.

Definition minSubArraySum_entail_wit_2_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((Znth i nums_l 0) >= min) |] 
  &&  [| (current >= 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nums_size_pre) |] 
  &&  [| ((Znth i nums_l 0) = (min_suffix_prefix ((i + 1 )) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix ((i + 1 )) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
.

Definition minSubArraySum_entail_wit_2_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| ((current + (Znth i nums_l 0) ) >= min) |] 
  &&  [| (current < 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nums_size_pre) |] 
  &&  [| ((current + (Znth i nums_l 0) ) = (min_suffix_prefix ((i + 1 )) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix ((i + 1 )) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
.

Definition minSubArraySum_return_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| (i >= nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (problem_114_spec_z nums_l min ) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
.

Definition minSubArraySum_partial_solve_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) ,
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  (((nums_pre + (0 * sizeof(INT64) ) )) # Int64  |-> (Znth 0 nums_l 0))
  **  (LongArray.missing_i nums_pre 0 0 nums_size_pre nums_l )
.

Definition minSubArraySum_partial_solve_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) ,
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |]
  &&  (((nums_pre + (0 * sizeof(INT64) ) )) # Int64  |-> (Znth 0 nums_l 0))
  **  (LongArray.missing_i nums_pre 0 0 nums_size_pre nums_l )
.

Definition minSubArraySum_partial_solve_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| (current < 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (current < 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (((nums_pre + (i * sizeof(INT64) ) )) # Int64  |-> (Znth i nums_l 0))
  **  (LongArray.missing_i nums_pre i 0 nums_size_pre nums_l )
.

Definition minSubArraySum_partial_solve_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (nums_l: (@list Z)) (min: Z) (current: Z) (i: Z) ,
  [| (current >= 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (LongArray.full nums_pre nums_size_pre nums_l )
|--
  [| (current >= 0) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (nums_l))) |] 
  &&  [| (problem_114_pre_z nums_l ) |] 
  &&  [| (kadane_int64_range nums_l ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (current = (min_suffix_prefix (i) (nums_l))) |] 
  &&  [| (min = (min_subarray_prefix (i) (nums_l))) |]
  &&  (((nums_pre + (i * sizeof(INT64) ) )) # Int64  |-> (Znth i nums_l 0))
  **  (LongArray.missing_i nums_pre i 0 nums_size_pre nums_l )
.

Module Type VC_Correct.

Include long_array_Strategy_Correct.

Axiom proof_of_minSubArraySum_safety_wit_1 : minSubArraySum_safety_wit_1.
Axiom proof_of_minSubArraySum_safety_wit_2 : minSubArraySum_safety_wit_2.
Axiom proof_of_minSubArraySum_safety_wit_3 : minSubArraySum_safety_wit_3.
Axiom proof_of_minSubArraySum_safety_wit_4 : minSubArraySum_safety_wit_4.
Axiom proof_of_minSubArraySum_safety_wit_5 : minSubArraySum_safety_wit_5.
Axiom proof_of_minSubArraySum_safety_wit_6 : minSubArraySum_safety_wit_6.
Axiom proof_of_minSubArraySum_safety_wit_7 : minSubArraySum_safety_wit_7.
Axiom proof_of_minSubArraySum_safety_wit_8 : minSubArraySum_safety_wit_8.
Axiom proof_of_minSubArraySum_safety_wit_9 : minSubArraySum_safety_wit_9.
Axiom proof_of_minSubArraySum_entail_wit_1 : minSubArraySum_entail_wit_1.
Axiom proof_of_minSubArraySum_entail_wit_2_1 : minSubArraySum_entail_wit_2_1.
Axiom proof_of_minSubArraySum_entail_wit_2_2 : minSubArraySum_entail_wit_2_2.
Axiom proof_of_minSubArraySum_entail_wit_2_3 : minSubArraySum_entail_wit_2_3.
Axiom proof_of_minSubArraySum_entail_wit_2_4 : minSubArraySum_entail_wit_2_4.
Axiom proof_of_minSubArraySum_return_wit_1 : minSubArraySum_return_wit_1.
Axiom proof_of_minSubArraySum_partial_solve_wit_1 : minSubArraySum_partial_solve_wit_1.
Axiom proof_of_minSubArraySum_partial_solve_wit_2 : minSubArraySum_partial_solve_wit_2.
Axiom proof_of_minSubArraySum_partial_solve_wit_3 : minSubArraySum_partial_solve_wit_3.
Axiom proof_of_minSubArraySum_partial_solve_wit_4 : minSubArraySum_partial_solve_wit_4.

End VC_Correct.
