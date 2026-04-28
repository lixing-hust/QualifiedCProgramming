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
Require Import coins_90.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function next_smallest -----*)

Definition next_smallest_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| ((lst_size_pre > 1) -> (lst_pre <> 0)) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition next_smallest_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (lst_size_pre <= 1) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| ((lst_size_pre > 1) -> (lst_pre <> 0)) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition next_smallest_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (lst_size_pre <= 1) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| ((lst_size_pre > 1) -> (lst_pre <> 0)) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition next_smallest_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (lst_pre <> 0) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.seg lst_pre 0 lst_size_pre input_l )
  **  (IntArray.undef_seg lst_pre lst_size_pre lst_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition next_smallest_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) ,
  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (lst_pre <> 0) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_full_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition next_smallest_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition next_smallest_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition next_smallest_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| ((Znth i sorted_l 0) = (Znth (i - 1 ) sorted_l 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition next_smallest_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full lst_pre lst_size_pre sorted_l )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition next_smallest_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full lst_pre lst_size_pre sorted_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition next_smallest_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (lst_size_pre > 1) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| ((lst_size_pre > 1) -> (lst_pre <> 0)) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_pre <> 0) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  (IntArray.seg lst_pre 0 lst_size_pre input_l )
  **  (IntArray.undef_seg lst_pre lst_size_pre lst_size_pre )
.

Definition next_smallest_entail_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) ,
  [| (lst_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (lst_pre <> 0) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_full_l )
|--
  EX (sorted_l: (@list Z)) ,
  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix 1 sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
.

Definition next_smallest_entail_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l_2: (@list Z)) ,
  [| ((Znth i sorted_l_2 0) = (Znth (i - 1 ) sorted_l_2 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l_2))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation input_l sorted_l_2 ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l_2 lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l_2 ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l_2 )
|--
  EX (sorted_l: (@list Z)) ,
  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix (i + 1 ) sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
.

Definition next_smallest_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
|--
  EX (final_l: (@list Z)) ,
  [| (problem_90_spec_z input_l (-1) ) |] 
  &&  [| (lst_size_pre = (Zlength (final_l))) |]
  &&  (IntArray.full lst_pre lst_size_pre final_l )
.

Definition next_smallest_return_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| ((Znth i sorted_l 0) <> (Znth (i - 1 ) sorted_l 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
|--
  EX (final_l: (@list Z)) ,
  [| (problem_90_spec_z input_l (Znth i sorted_l 0) ) |] 
  &&  [| (lst_size_pre = (Zlength (final_l))) |]
  &&  (IntArray.full lst_pre lst_size_pre final_l )
.

Definition next_smallest_return_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (lst_size_pre <= 1) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| ((lst_size_pre > 1) -> (lst_pre <> 0)) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  EX (final_l: (@list Z)) ,
  [| (problem_90_spec_z input_l (-1) ) |] 
  &&  [| (lst_size_pre = (Zlength (final_l))) |]
  &&  (IntArray.full lst_pre lst_size_pre final_l )
.

Definition next_smallest_partial_solve_wit_1_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (lst_pre <> 0) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.seg lst_pre 0 lst_size_pre input_l )
  **  (IntArray.undef_seg lst_pre lst_size_pre lst_size_pre )
|--
  [| (lst_pre <> 0) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
.

Definition next_smallest_partial_solve_wit_1_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (lst_pre <> 0) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  (IntArray.seg lst_pre 0 lst_size_pre input_l )
  **  (IntArray.undef_seg lst_pre lst_size_pre lst_size_pre )
|--
  [| (lst_pre <> 0) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_pre <> 0) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |]
  &&  (IntArray.seg lst_pre 0 lst_size_pre input_l )
  **  (IntArray.undef_seg lst_pre lst_size_pre lst_size_pre )
.

Definition next_smallest_partial_solve_wit_1 := next_smallest_partial_solve_wit_1_pure -> next_smallest_partial_solve_wit_1_aux.

Definition next_smallest_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i sorted_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre sorted_l )
.

Definition next_smallest_partial_solve_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (((lst_pre + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (i - 1 ) sorted_l 0))
  **  (IntArray.missing_i lst_pre (i - 1 ) 0 lst_size_pre sorted_l )
.

Definition next_smallest_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted_l: (@list Z)) ,
  [| ((Znth i sorted_l 0) <> (Znth (i - 1 ) sorted_l 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre sorted_l )
|--
  [| ((Znth i sorted_l 0) <> (Znth (i - 1 ) sorted_l 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (lst_size_pre = (Zlength (sorted_l))) |] 
  &&  [| (problem_90_pre_z input_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation input_l sorted_l ) |] 
  &&  [| (next_smallest_sorted_bridge input_l sorted_l lst_size_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (no_distinct_prefix i sorted_l ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i sorted_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre sorted_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_next_smallest_safety_wit_1 : next_smallest_safety_wit_1.
Axiom proof_of_next_smallest_safety_wit_2 : next_smallest_safety_wit_2.
Axiom proof_of_next_smallest_safety_wit_3 : next_smallest_safety_wit_3.
Axiom proof_of_next_smallest_safety_wit_4 : next_smallest_safety_wit_4.
Axiom proof_of_next_smallest_safety_wit_5 : next_smallest_safety_wit_5.
Axiom proof_of_next_smallest_safety_wit_6 : next_smallest_safety_wit_6.
Axiom proof_of_next_smallest_safety_wit_7 : next_smallest_safety_wit_7.
Axiom proof_of_next_smallest_safety_wit_8 : next_smallest_safety_wit_8.
Axiom proof_of_next_smallest_safety_wit_9 : next_smallest_safety_wit_9.
Axiom proof_of_next_smallest_safety_wit_10 : next_smallest_safety_wit_10.
Axiom proof_of_next_smallest_entail_wit_1 : next_smallest_entail_wit_1.
Axiom proof_of_next_smallest_entail_wit_2 : next_smallest_entail_wit_2.
Axiom proof_of_next_smallest_entail_wit_3 : next_smallest_entail_wit_3.
Axiom proof_of_next_smallest_return_wit_1 : next_smallest_return_wit_1.
Axiom proof_of_next_smallest_return_wit_2 : next_smallest_return_wit_2.
Axiom proof_of_next_smallest_return_wit_3 : next_smallest_return_wit_3.
Axiom proof_of_next_smallest_partial_solve_wit_1_pure : next_smallest_partial_solve_wit_1_pure.
Axiom proof_of_next_smallest_partial_solve_wit_1 : next_smallest_partial_solve_wit_1.
Axiom proof_of_next_smallest_partial_solve_wit_2 : next_smallest_partial_solve_wit_2.
Axiom proof_of_next_smallest_partial_solve_wit_3 : next_smallest_partial_solve_wit_3.
Axiom proof_of_next_smallest_partial_solve_wit_4 : next_smallest_partial_solve_wit_4.

End VC_Correct.
