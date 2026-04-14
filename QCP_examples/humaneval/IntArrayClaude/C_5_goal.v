Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_5.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function intersperse -----*)

Definition intersperse_safety_wit_1 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (numbers_size0 = 0) |] 
  &&  [| (out_size0 = 0) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_2 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_3 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_4 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (numbers_size0 = 0) |] 
  &&  [| (out_size0 = 0) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_5 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre = 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| False |]
.

Definition intersperse_safety_wit_6 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (numbers_size0 = 0) |] 
  &&  [| (out_size0 = 0) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| False |]
.

Definition intersperse_safety_wit_7 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_8 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 input_l 0))
  **  (IntArray.undef_seg out_pre 1 out_size_pre )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition intersperse_safety_wit_9 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 input_l 0))
  **  (IntArray.undef_seg out_pre 1 out_size_pre )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_10 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 input_l 0))
  **  (IntArray.undef_seg out_pre 1 out_size_pre )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "k" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_11 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  (IntArray.undef_seg out0 (k + 1 ) out_size0 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition intersperse_safety_wit_12 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  (IntArray.undef_seg out0 (k + 1 ) out_size0 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_13 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg out0 ((k + 1 ) + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| (((k + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((k + 1 ) + 1 )) |]
.

Definition intersperse_safety_wit_14 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg out0 ((k + 1 ) + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_15 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg out0 ((k + 1 ) + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition intersperse_entail_wit_1 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 input_l 0))
  **  (IntArray.undef_seg out_pre 1 out_size_pre )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  [| (1 <= 1) |] 
  &&  [| (1 <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| ((0 + 1 ) = ((2 * 1 ) - 1 )) |]
  &&  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 (0 + 1 ) (intersperse_list ((sublist (0) (1) (input_l))) (delimeter0)) )
  **  (IntArray.undef_seg out0 (0 + 1 ) out_size0 )
.

Definition intersperse_entail_wit_2 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg out0 ((k + 1 ) + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (((k + 1 ) + 1 ) = ((2 * (i + 1 ) ) - 1 )) |]
  &&  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 ((k + 1 ) + 1 ) (intersperse_list ((sublist (0) ((i + 1 )) (input_l))) (delimeter0)) )
  **  (IntArray.undef_seg out0 ((k + 1 ) + 1 ) out_size0 )
.

Definition intersperse_return_wit_1 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre = 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (numbers_size0 = 0) |] 
  &&  [| (out_size0 = 0) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out_pre = out0) |] 
  &&  [| (problem_5_pre input_l output_l ) |] 
  &&  [| (problem_5_spec input_l output_l delimeter0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.full out0 out_size0 output_l )
.

Definition intersperse_return_wit_2 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i >= numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
  **  (IntArray.undef_seg out0 k out_size0 )
|--
  EX (output_l: (@list Z)) ,
  [| (out0 = out0) |] 
  &&  [| (problem_5_pre input_l output_l ) |] 
  &&  [| (problem_5_spec input_l output_l delimeter0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.full out0 out_size0 output_l )
.

Definition intersperse_partial_solve_wit_1 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (((numbers_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 input_l 0))
  **  (IntArray.missing_i numbers_pre 0 0 numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
.

Definition intersperse_partial_solve_wit_2 := 
forall (out_size_pre: Z) (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  [| (numbers_size_pre <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (delimeter_pre = delimeter0) |] 
  &&  [| (out_pre = out0) |] 
  &&  [| (out_size_pre = out_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (0 < numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 <= out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (int_value_range delimeter0 ) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre 1 out_size_pre )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
.

Definition intersperse_partial_solve_wit_3 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
  **  (IntArray.undef_seg out0 k out_size0 )
|--
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out0 (k + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
.

Definition intersperse_partial_solve_wit_4 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  (IntArray.undef_seg out0 (k + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((numbers0 + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i numbers0 i 0 numbers_size0 input_l )
  **  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  (IntArray.undef_seg out0 (k + 1 ) out_size0 )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
.

Definition intersperse_partial_solve_wit_5 := 
forall (out_size0: Z) (out0: Z) (delimeter0: Z) (numbers_size0: Z) (numbers0: Z) (input_l: (@list Z)) (k: Z) (i: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (IntArray.full numbers0 numbers_size0 input_l )
  **  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  (IntArray.undef_seg out0 (k + 1 ) out_size0 )
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
|--
  [| (i < numbers_size0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (out_size0 = ((2 * numbers_size0 ) - 1 )) |] 
  &&  [| (0 < out_size0) |] 
  &&  [| (out_size0 < INT_MAX) |] 
  &&  [| (k = ((2 * i ) - 1 )) |]
  &&  (((out0 + ((k + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out0 ((k + 1 ) + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 input_l )
  **  (((out0 + (k * sizeof(INT) ) )) # Int  |-> delimeter0)
  **  (IntArray.seg out0 0 k (intersperse_list ((sublist (0) (i) (input_l))) (delimeter0)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_intersperse_safety_wit_1 : intersperse_safety_wit_1.
Axiom proof_of_intersperse_safety_wit_2 : intersperse_safety_wit_2.
Axiom proof_of_intersperse_safety_wit_3 : intersperse_safety_wit_3.
Axiom proof_of_intersperse_safety_wit_4 : intersperse_safety_wit_4.
Axiom proof_of_intersperse_safety_wit_5 : intersperse_safety_wit_5.
Axiom proof_of_intersperse_safety_wit_6 : intersperse_safety_wit_6.
Axiom proof_of_intersperse_safety_wit_7 : intersperse_safety_wit_7.
Axiom proof_of_intersperse_safety_wit_8 : intersperse_safety_wit_8.
Axiom proof_of_intersperse_safety_wit_9 : intersperse_safety_wit_9.
Axiom proof_of_intersperse_safety_wit_10 : intersperse_safety_wit_10.
Axiom proof_of_intersperse_safety_wit_11 : intersperse_safety_wit_11.
Axiom proof_of_intersperse_safety_wit_12 : intersperse_safety_wit_12.
Axiom proof_of_intersperse_safety_wit_13 : intersperse_safety_wit_13.
Axiom proof_of_intersperse_safety_wit_14 : intersperse_safety_wit_14.
Axiom proof_of_intersperse_safety_wit_15 : intersperse_safety_wit_15.
Axiom proof_of_intersperse_entail_wit_1 : intersperse_entail_wit_1.
Axiom proof_of_intersperse_entail_wit_2 : intersperse_entail_wit_2.
Axiom proof_of_intersperse_return_wit_1 : intersperse_return_wit_1.
Axiom proof_of_intersperse_return_wit_2 : intersperse_return_wit_2.
Axiom proof_of_intersperse_partial_solve_wit_1 : intersperse_partial_solve_wit_1.
Axiom proof_of_intersperse_partial_solve_wit_2 : intersperse_partial_solve_wit_2.
Axiom proof_of_intersperse_partial_solve_wit_3 : intersperse_partial_solve_wit_3.
Axiom proof_of_intersperse_partial_solve_wit_4 : intersperse_partial_solve_wit_4.
Axiom proof_of_intersperse_partial_solve_wit_5 : intersperse_partial_solve_wit_5.

End VC_Correct.
