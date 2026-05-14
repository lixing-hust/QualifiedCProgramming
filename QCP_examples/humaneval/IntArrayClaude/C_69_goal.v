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
Require Import coins_69.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function search -----*)

Definition search_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "freq_size" ) )) # Int  |->_)
  **  ((( &( "cnts" ) )) # Ptr  |->_)
  **  ((( &( "vals" ) )) # Ptr  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |->_)
  **  ((( &( "vals" ) )) # Ptr  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition search_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |->_)
  **  ((( &( "vals" ) )) # Ptr  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| False |]
.

Definition search_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| False |]
.

Definition search_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "has" ) )) # Int  |->_)
  **  ((( &( "current" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "current" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "current" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |-> retval_2)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (j: Z) (has: Z) (cnts: Z) (vals: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (j: Z) (cnts: Z) (vals: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (((Znth (j - 0 ) cnts_l 0) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth (j - 0 ) cnts_l 0) + 1 )) |]
.

Definition search_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current <> (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition search_safety_wit_18 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_19 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 1) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition search_safety_wit_20 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (has <> 0) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| False |]
.

Definition search_safety_wit_21 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (has = 0) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 1) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| False |]
.

Definition search_safety_wit_22 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_23 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
|--
  [| ((freq_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (freq_size + 1 )) |]
.

Definition search_safety_wit_24 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_25 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> (freq_size + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition search_safety_wit_26 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> (freq_size + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_27 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (max = (-1)) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> (freq_size + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_28 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (current = 1) |] 
  &&  [| (max = (-1)) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> (freq_size + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition search_safety_wit_29 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (j: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= (i + 1 )) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l (i + 1 ) vals_l cnts_l max ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition search_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.undef_full retval lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (Zlength (vals_l))) |] 
  &&  [| (0 = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= (-1)) |] 
  &&  [| ((-1) < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l 0 vals_l cnts_l (-1) ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg retval 0 0 vals_l )
  **  (IntArray.undef_seg retval 0 lst_size_pre )
  **  (IntArray.seg retval_2 0 0 cnts_l )
  **  (IntArray.undef_seg retval_2 0 lst_size_pre )
.

Definition search_entail_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l_2: (@list Z)) (vals_l_2: (@list Z)) (freq_size: Z) (i: Z) (cnts: Z) (vals: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l_2 cnts_l_2 max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| ((Znth i input_l 0) = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < (Znth i input_l 0)) |] 
  &&  [| ((Znth i input_l 0) < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i 0 vals_l cnts_l 0 max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_entail_wit_3_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l_2: (@list Z)) (vals_l_2: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (j >= freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l_2 cnts_l_2 has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  (EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
  ||
  (EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 1) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
.

Definition search_entail_wit_3_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l_2: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| ((Znth (j - 0 ) vals_l 0) > max) |] 
  &&  [| ((Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l_2 0) + 1 )) (cnts_l_2)) 0) >= (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l_2 has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l_2 0) + 1 )) (cnts_l_2)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  (EX (cnts_l: (@list Z))  (vals_l_2: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (1 = 0) |] 
  &&  [| ((-1) <= (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| ((Znth (j - 0 ) vals_l 0) < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l_2 cnts_l 1 (Znth (j - 0 ) vals_l 0) ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
  ||
  (EX (cnts_l: (@list Z))  (vals_l_2: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (1 = 1) |] 
  &&  [| ((-1) <= (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| ((Znth (j - 0 ) vals_l 0) < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l_2 cnts_l 1 (Znth (j - 0 ) vals_l 0) ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
.

Definition search_entail_wit_3_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l_2: (@list Z)) (vals_l_2: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| ((Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l_2 0) + 1 )) (cnts_l_2)) 0) < (Znth (j - 0 ) vals_l_2 0)) |] 
  &&  [| (current = (Znth (j - 0 ) vals_l_2 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l_2 cnts_l_2 has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l_2 0) + 1 )) (cnts_l_2)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  (EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (1 = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l 1 max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
  ||
  (EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (1 = 1) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l 1 max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
.

Definition search_entail_wit_3_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l_2: (@list Z)) (vals_l_2: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| ((Znth (j - 0 ) vals_l_2 0) <= max) |] 
  &&  [| ((Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l_2 0) + 1 )) (cnts_l_2)) 0) >= (Znth (j - 0 ) vals_l_2 0)) |] 
  &&  [| (current = (Znth (j - 0 ) vals_l_2 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l_2 cnts_l_2 has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l_2 0) + 1 )) (cnts_l_2)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  (EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (1 = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l 1 max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
  ||
  (EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (1 = 1) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l 1 max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre ))
.

Definition search_entail_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l_2: (@list Z)) (vals_l_2: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current <> (Znth (j - 0 ) vals_l_2 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l_2 cnts_l_2 has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i (j + 1 ) vals_l cnts_l has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_entail_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (has: Z) (max: Z) ,
  [| (has = 0) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l_2 cnts_l_2 has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size (freq_size + 1 ) )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size (freq_size + 1 ) )
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
.

Definition search_entail_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l_2 cnts_l_2 has max ) |]
  &&  (((vals + (freq_size * sizeof(INT) ) )) # Int  |-> current)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size (freq_size + 1 ) )
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_entail_wit_7_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (max: Z) ,
  [| (current = 1) |] 
  &&  [| (max = (-1)) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l_2 cnts_l_2 max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l_2 )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= (freq_size + 1 )) |] 
  &&  [| ((freq_size + 1 ) <= (i + 1 )) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= 1) |] 
  &&  [| (1 < INT_MAX) |] 
  &&  [| (search_outer_add_new_69 input_l i vals_l cnts_l 1 (Znth (i) (input_l) (0)) (freq_size + 1 ) 1 ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 (freq_size + 1 ) cnts_l )
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
.

Definition search_entail_wit_7_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (max: Z) ,
  [| (max <> (-1)) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l_2 cnts_l_2 max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l_2 )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= (freq_size + 1 )) |] 
  &&  [| ((freq_size + 1 ) <= (i + 1 )) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_add_new_69 input_l i vals_l cnts_l max (Znth (i) (input_l) (0)) (freq_size + 1 ) 1 ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 (freq_size + 1 ) cnts_l )
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
.

Definition search_entail_wit_7_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (max: Z) ,
  [| (current <> 1) |] 
  &&  [| (max = (-1)) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l_2 cnts_l_2 max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l_2 )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= (freq_size + 1 )) |] 
  &&  [| ((freq_size + 1 ) <= (i + 1 )) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_add_new_69 input_l i vals_l cnts_l max (Znth (i) (input_l) (0)) (freq_size + 1 ) 1 ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 (freq_size + 1 ) cnts_l )
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
.

Definition search_entail_wit_8_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= (i + 1 )) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_add_new_69 input_l i vals_l_2 cnts_l_2 max (Znth (i) (input_l) (0)) freq_size 1 ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= (i + 1 )) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l (i + 1 ) vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_entail_wit_8_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (has: Z) (max: Z) ,
  [| (has <> 0) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| (has = 1) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l_2 cnts_l_2 has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= (i + 1 )) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l (i + 1 ) vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_entail_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l_2: (@list Z)) (cnts_l_2: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= (i + 1 )) |] 
  &&  [| (freq_size = (Zlength (vals_l_2))) |] 
  &&  [| (freq_size = (Zlength (cnts_l_2))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l (i + 1 ) vals_l_2 cnts_l_2 max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l_2 )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l_2 )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  EX (cnts_l: (@list Z))  (vals_l: (@list Z)) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= (i + 1 )) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l (i + 1 ) vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (cnts: Z) (vals: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (problem_69_spec input_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition search_partial_solve_wit_1_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |->_)
  **  ((( &( "vals" ) )) # Ptr  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
.

Definition search_partial_solve_wit_1_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition search_partial_solve_wit_1 := search_partial_solve_wit_1_pure -> search_partial_solve_wit_1_aux.

Definition search_partial_solve_wit_2_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval lst_size_pre )
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "freq_size" ) )) # Int  |-> 0)
  **  ((( &( "cnts" ) )) # Ptr  |->_)
  **  ((( &( "vals" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
.

Definition search_partial_solve_wit_2_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (lst_size_pre >= 0) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |]
  &&  (IntArray.undef_full retval lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition search_partial_solve_wit_2 := search_partial_solve_wit_2_pure -> search_partial_solve_wit_2_aux.

Definition search_partial_solve_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (cnts: Z) (vals: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (((vals + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) vals_l 0))
  **  (IntArray.missing_i vals j 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (((cnts + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) cnts_l 0))
  **  (IntArray.missing_i cnts j 0 freq_size cnts_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (((cnts + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i cnts j 0 freq_size cnts_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (((cnts + (j * sizeof(INT) ) )) # Int  |-> (Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) 0))
  **  (IntArray.missing_i cnts j 0 freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (((vals + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) vals_l 0))
  **  (IntArray.missing_i vals j 0 freq_size vals_l )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| ((Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) 0) >= (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| ((Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) 0) >= (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (((vals + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) vals_l 0))
  **  (IntArray.missing_i vals j 0 freq_size vals_l )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (has: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (j: Z) (i: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| ((Znth (j - 0 ) vals_l 0) > max) |] 
  &&  [| ((Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) 0) >= (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| ((Znth (j - 0 ) vals_l 0) > max) |] 
  &&  [| ((Znth j (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) 0) >= (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (current = (Znth (j - 0 ) vals_l 0)) |] 
  &&  [| (j < freq_size) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= freq_size) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_state_69 input_l i j vals_l cnts_l has max ) |]
  &&  (((vals + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) vals_l 0))
  **  (IntArray.missing_i vals j 0 freq_size vals_l )
  **  (IntArray.full cnts freq_size (replace_Znth (j) (((Znth (j - 0 ) cnts_l 0) + 1 )) (cnts_l)) )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (has: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size (freq_size + 1 ) )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size (freq_size + 1 ) )
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
|--
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (has = 0) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_inner_to_outer_69 input_l i vals_l cnts_l has max ) |]
  &&  (((vals + (freq_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size (freq_size + 1 ) )
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
.

Definition search_partial_solve_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (vals_l: (@list Z)) (cnts_l: (@list Z)) (vals: Z) (cnts: Z) (current: Z) (i: Z) (freq_size: Z) (max: Z) ,
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (0 < current) |] 
  &&  [| (current < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size < lst_size_pre) |] 
  &&  [| ((freq_size + 1 ) = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_after_val_write_69 input_l i vals_l cnts_l max current freq_size ) |]
  &&  (((cnts + (freq_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg cnts (freq_size + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 (freq_size + 1 ) vals_l )
  **  (IntArray.undef_seg vals (freq_size + 1 ) lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
.

Definition search_partial_solve_wit_13_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (j: Z) (has: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (vals <> 0) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |]
.

Definition search_partial_solve_wit_13_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (cnts: Z) (vals: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (vals <> 0) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.seg vals 0 freq_size vals_l )
  **  (IntArray.undef_seg vals freq_size lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
.

Definition search_partial_solve_wit_13 := search_partial_solve_wit_13_pure -> search_partial_solve_wit_13_aux.

Definition search_partial_solve_wit_14_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (j: Z) (has: Z) (current: Z) (cnts: Z) (vals: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "cnts" ) )) # Ptr  |-> cnts)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "freq_size" ) )) # Int  |-> freq_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (cnts <> 0) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |]
.

Definition search_partial_solve_wit_14_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (max: Z) (cnts_l: (@list Z)) (vals_l: (@list Z)) (freq_size: Z) (i: Z) (cnts: Z) (vals: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
|--
  [| (cnts <> 0) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (vals <> 0) |] 
  &&  [| (cnts <> 0) |] 
  &&  [| (0 < lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_69_pre input_l ) |] 
  &&  [| (search_int_range_69 input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (0 <= freq_size) |] 
  &&  [| (freq_size <= i) |] 
  &&  [| (freq_size = (Zlength (vals_l))) |] 
  &&  [| (freq_size = (Zlength (cnts_l))) |] 
  &&  [| ((-1) <= max) |] 
  &&  [| (max < INT_MAX) |] 
  &&  [| (search_outer_state_69 input_l i vals_l cnts_l max ) |]
  &&  (IntArray.seg cnts 0 freq_size cnts_l )
  **  (IntArray.undef_seg cnts freq_size lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition search_partial_solve_wit_14 := search_partial_solve_wit_14_pure -> search_partial_solve_wit_14_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_search_safety_wit_1 : search_safety_wit_1.
Axiom proof_of_search_safety_wit_2 : search_safety_wit_2.
Axiom proof_of_search_safety_wit_3 : search_safety_wit_3.
Axiom proof_of_search_safety_wit_4 : search_safety_wit_4.
Axiom proof_of_search_safety_wit_5 : search_safety_wit_5.
Axiom proof_of_search_safety_wit_6 : search_safety_wit_6.
Axiom proof_of_search_safety_wit_7 : search_safety_wit_7.
Axiom proof_of_search_safety_wit_8 : search_safety_wit_8.
Axiom proof_of_search_safety_wit_9 : search_safety_wit_9.
Axiom proof_of_search_safety_wit_10 : search_safety_wit_10.
Axiom proof_of_search_safety_wit_11 : search_safety_wit_11.
Axiom proof_of_search_safety_wit_12 : search_safety_wit_12.
Axiom proof_of_search_safety_wit_13 : search_safety_wit_13.
Axiom proof_of_search_safety_wit_14 : search_safety_wit_14.
Axiom proof_of_search_safety_wit_15 : search_safety_wit_15.
Axiom proof_of_search_safety_wit_16 : search_safety_wit_16.
Axiom proof_of_search_safety_wit_17 : search_safety_wit_17.
Axiom proof_of_search_safety_wit_18 : search_safety_wit_18.
Axiom proof_of_search_safety_wit_19 : search_safety_wit_19.
Axiom proof_of_search_safety_wit_20 : search_safety_wit_20.
Axiom proof_of_search_safety_wit_21 : search_safety_wit_21.
Axiom proof_of_search_safety_wit_22 : search_safety_wit_22.
Axiom proof_of_search_safety_wit_23 : search_safety_wit_23.
Axiom proof_of_search_safety_wit_24 : search_safety_wit_24.
Axiom proof_of_search_safety_wit_25 : search_safety_wit_25.
Axiom proof_of_search_safety_wit_26 : search_safety_wit_26.
Axiom proof_of_search_safety_wit_27 : search_safety_wit_27.
Axiom proof_of_search_safety_wit_28 : search_safety_wit_28.
Axiom proof_of_search_safety_wit_29 : search_safety_wit_29.
Axiom proof_of_search_entail_wit_1 : search_entail_wit_1.
Axiom proof_of_search_entail_wit_2 : search_entail_wit_2.
Axiom proof_of_search_entail_wit_3_1 : search_entail_wit_3_1.
Axiom proof_of_search_entail_wit_3_2 : search_entail_wit_3_2.
Axiom proof_of_search_entail_wit_3_3 : search_entail_wit_3_3.
Axiom proof_of_search_entail_wit_3_4 : search_entail_wit_3_4.
Axiom proof_of_search_entail_wit_4 : search_entail_wit_4.
Axiom proof_of_search_entail_wit_5 : search_entail_wit_5.
Axiom proof_of_search_entail_wit_6 : search_entail_wit_6.
Axiom proof_of_search_entail_wit_7_1 : search_entail_wit_7_1.
Axiom proof_of_search_entail_wit_7_2 : search_entail_wit_7_2.
Axiom proof_of_search_entail_wit_7_3 : search_entail_wit_7_3.
Axiom proof_of_search_entail_wit_8_1 : search_entail_wit_8_1.
Axiom proof_of_search_entail_wit_8_2 : search_entail_wit_8_2.
Axiom proof_of_search_entail_wit_9 : search_entail_wit_9.
Axiom proof_of_search_return_wit_1 : search_return_wit_1.
Axiom proof_of_search_partial_solve_wit_1_pure : search_partial_solve_wit_1_pure.
Axiom proof_of_search_partial_solve_wit_1 : search_partial_solve_wit_1.
Axiom proof_of_search_partial_solve_wit_2_pure : search_partial_solve_wit_2_pure.
Axiom proof_of_search_partial_solve_wit_2 : search_partial_solve_wit_2.
Axiom proof_of_search_partial_solve_wit_3 : search_partial_solve_wit_3.
Axiom proof_of_search_partial_solve_wit_4 : search_partial_solve_wit_4.
Axiom proof_of_search_partial_solve_wit_5 : search_partial_solve_wit_5.
Axiom proof_of_search_partial_solve_wit_6 : search_partial_solve_wit_6.
Axiom proof_of_search_partial_solve_wit_7 : search_partial_solve_wit_7.
Axiom proof_of_search_partial_solve_wit_8 : search_partial_solve_wit_8.
Axiom proof_of_search_partial_solve_wit_9 : search_partial_solve_wit_9.
Axiom proof_of_search_partial_solve_wit_10 : search_partial_solve_wit_10.
Axiom proof_of_search_partial_solve_wit_11 : search_partial_solve_wit_11.
Axiom proof_of_search_partial_solve_wit_12 : search_partial_solve_wit_12.
Axiom proof_of_search_partial_solve_wit_13_pure : search_partial_solve_wit_13_pure.
Axiom proof_of_search_partial_solve_wit_13 : search_partial_solve_wit_13.
Axiom proof_of_search_partial_solve_wit_14_pure : search_partial_solve_wit_14_pure.
Axiom proof_of_search_partial_solve_wit_14 : search_partial_solve_wit_14.

End VC_Correct.
