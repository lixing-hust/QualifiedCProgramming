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
Require Import coins_128.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function abs -----*)

Definition abs_safety_wit_1 := 
forall (x_pre: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition abs_safety_wit_2 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (x_pre <> (INT_MIN)) |]
.

Definition abs_return_wit_1 := 
forall (x_pre: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| (x_pre = (Zabs (x_pre))) |]
  &&  emp
.

Definition abs_return_wit_2 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((-x_pre) = (Zabs (x_pre))) |]
  &&  emp
.

(*----- Function prod_signs -----*)

Definition prod_signs_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prod_signs_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_size_pre = 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (32768 <> (INT_MIN)) |]
.

Definition prod_signs_safety_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_size_pre = 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (32768 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32768) |]
.

Definition prod_signs_safety_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  ((( &( "prods" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition prod_signs_safety_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prod_signs_safety_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  ((( &( "prods" ) )) # Int  |-> 1)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prod_signs_safety_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "mag" ) )) # Int  |-> mag)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + mag )) |]
.

Definition prod_signs_safety_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "mag" ) )) # Int  |-> mag)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prod_signs_safety_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current = 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "mag" ) )) # Int  |-> mag)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prod_signs_safety_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current <> 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "mag" ) )) # Int  |-> mag)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prod_signs_safety_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current = 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "mag" ) )) # Int  |-> mag)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prod_signs_safety_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current < 0) |] 
  &&  [| (current = 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "mag" ) )) # Int  |-> mag)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| False |]
.

Definition prod_signs_safety_wit_13 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current < 0) |] 
  &&  [| (current <> 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "mag" ) )) # Int  |-> mag)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (prods <> (INT_MIN)) |]
.

Definition prod_signs_safety_wit_14 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current >= 0) |] 
  &&  [| (current = 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition prod_signs_safety_wit_15 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current >= 0) |] 
  &&  [| (current <> 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition prod_signs_safety_wit_16 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current < 0) |] 
  &&  [| (current <> 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> (-prods))
  **  ((( &( "sum" ) )) # Int  |-> (sum + mag ))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition prod_signs_safety_wit_17 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sum: Z) (prods: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| ((sum * prods ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum * prods )) |]
.

Definition prod_signs_entail_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix 0 input_l 0 1 ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_entail_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sum: Z) (prods: Z) (i: Z) (retval: Z) ,
  [| (retval = (Zabs ((Znth i input_l 0)))) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| ((Znth i input_l 0) = (Znth (i) (input_l) (0))) |] 
  &&  [| (retval = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + retval )) |] 
  &&  [| ((sum + retval ) <= INT_MAX) |] 
  &&  [| (INT_MIN < (Znth i input_l 0)) |] 
  &&  [| ((Znth i input_l 0) <= INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_entail_wit_3_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current < 0) |] 
  &&  [| (current <> 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix (i + 1 ) input_l (sum + mag ) (-prods) ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_entail_wit_3_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current >= 0) |] 
  &&  [| (current <> 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix (i + 1 ) input_l (sum + mag ) prods ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_entail_wit_3_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (prods: Z) (sum: Z) (current: Z) (mag: Z) ,
  [| (current >= 0) |] 
  &&  [| (current = 0) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |] 
  &&  [| (current = (Znth (i) (input_l) (0))) |] 
  &&  [| (mag = (Zabs ((Znth (i) (input_l) (0))))) |] 
  &&  [| (INT_MIN <= (sum + mag )) |] 
  &&  [| ((sum + mag ) <= INT_MAX) |] 
  &&  [| (INT_MIN < current) |] 
  &&  [| (current <= INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix (i + 1 ) input_l (sum + mag ) 0 ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sum: Z) (prods: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (problem_128_spec_z input_l (sum * prods ) ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_return_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (arr_size_pre = 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (problem_128_spec_z input_l (-32768) ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sum: Z) (prods: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
.

Definition prod_signs_partial_solve_wit_2_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sum: Z) (prods: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  ((( &( "mag" ) )) # Int  |->_)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prods" ) )) # Int  |-> prods)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| ((Znth i input_l 0) <= INT_MAX) |] 
  &&  [| (INT_MIN < (Znth i input_l 0)) |]
.

Definition prod_signs_partial_solve_wit_2_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sum: Z) (prods: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| ((Znth i input_l 0) <= INT_MAX) |] 
  &&  [| (INT_MIN < (Znth i input_l 0)) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (arr_size_pre <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_128_pre_z input_l ) |] 
  &&  [| (prod_signs_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (prod_signs_prefix i input_l sum prods ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition prod_signs_partial_solve_wit_2 := prod_signs_partial_solve_wit_2_pure -> prod_signs_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_prod_signs_safety_wit_1 : prod_signs_safety_wit_1.
Axiom proof_of_prod_signs_safety_wit_2 : prod_signs_safety_wit_2.
Axiom proof_of_prod_signs_safety_wit_3 : prod_signs_safety_wit_3.
Axiom proof_of_prod_signs_safety_wit_4 : prod_signs_safety_wit_4.
Axiom proof_of_prod_signs_safety_wit_5 : prod_signs_safety_wit_5.
Axiom proof_of_prod_signs_safety_wit_6 : prod_signs_safety_wit_6.
Axiom proof_of_prod_signs_safety_wit_7 : prod_signs_safety_wit_7.
Axiom proof_of_prod_signs_safety_wit_8 : prod_signs_safety_wit_8.
Axiom proof_of_prod_signs_safety_wit_9 : prod_signs_safety_wit_9.
Axiom proof_of_prod_signs_safety_wit_10 : prod_signs_safety_wit_10.
Axiom proof_of_prod_signs_safety_wit_11 : prod_signs_safety_wit_11.
Axiom proof_of_prod_signs_safety_wit_12 : prod_signs_safety_wit_12.
Axiom proof_of_prod_signs_safety_wit_13 : prod_signs_safety_wit_13.
Axiom proof_of_prod_signs_safety_wit_14 : prod_signs_safety_wit_14.
Axiom proof_of_prod_signs_safety_wit_15 : prod_signs_safety_wit_15.
Axiom proof_of_prod_signs_safety_wit_16 : prod_signs_safety_wit_16.
Axiom proof_of_prod_signs_safety_wit_17 : prod_signs_safety_wit_17.
Axiom proof_of_prod_signs_entail_wit_1 : prod_signs_entail_wit_1.
Axiom proof_of_prod_signs_entail_wit_2 : prod_signs_entail_wit_2.
Axiom proof_of_prod_signs_entail_wit_3_1 : prod_signs_entail_wit_3_1.
Axiom proof_of_prod_signs_entail_wit_3_2 : prod_signs_entail_wit_3_2.
Axiom proof_of_prod_signs_entail_wit_3_3 : prod_signs_entail_wit_3_3.
Axiom proof_of_prod_signs_return_wit_1 : prod_signs_return_wit_1.
Axiom proof_of_prod_signs_return_wit_2 : prod_signs_return_wit_2.
Axiom proof_of_prod_signs_partial_solve_wit_1 : prod_signs_partial_solve_wit_1.
Axiom proof_of_prod_signs_partial_solve_wit_2_pure : prod_signs_partial_solve_wit_2_pure.
Axiom proof_of_prod_signs_partial_solve_wit_2 : prod_signs_partial_solve_wit_2.

End VC_Correct.
