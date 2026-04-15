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
Require Import coins_8.
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

(*----- Function sum_product -----*)

Definition sum_product_safety_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sum_product_safety_wit_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sum_product_safety_wit_3 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "product" ) )) # Int  |-> 1)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition sum_product_safety_wit_4 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "product" ) )) # Int  |-> 1)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sum_product_safety_wit_5 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.undef_full out 2 )
|--
  [| ((sum + (Znth i lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (Znth i lv 0) )) |]
.

Definition sum_product_safety_wit_6 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i lv 0) ))
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.undef_full out 2 )
|--
  [| ((product * (Znth i lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (product * (Znth i lv 0) )) |]
.

Definition sum_product_safety_wit_7 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i lv 0) ))
  **  ((( &( "product" ) )) # Int  |-> (product * (Znth i lv 0) ))
  **  (IntArray.undef_full out 2 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sum_product_safety_wit_8 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i >= numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sum_product_safety_wit_9 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i >= numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (((out + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.undef_seg out 1 2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full numbers0 numbers_size0 lv )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sum_product_entail_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.undef_full retval 2 )
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (0 = (prefix_sum (lv) (0))) |] 
  &&  [| (1 = (prefix_product (lv) (0))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.undef_full retval 2 )
.

Definition sum_product_entail_wit_2 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
|--
  [| (out <> 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size0) |] 
  &&  [| ((sum + (Znth i lv 0) ) = (prefix_sum (lv) ((i + 1 )))) |] 
  &&  [| ((product * (Znth i lv 0) ) = (prefix_product (lv) ((i + 1 )))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
.

Definition sum_product_return_wit_1 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i >= numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (((out + (1 * sizeof(INT) ) )) # Int  |-> product)
  **  (((out + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.full numbers0 numbers_size0 lv )
|--
  EX (s: Z)  (p: Z) ,
  [| (out <> 0) |] 
  &&  [| (problem_8_spec lv s p ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.full out 2 (cons (s) ((cons (p) (nil)))) )
.

Definition sum_product_partial_solve_wit_1_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "product" ) )) # Int  |-> 1)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |]
.

Definition sum_product_partial_solve_wit_1_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |] 
  &&  [| (numbers_pre = numbers0) |] 
  &&  [| (numbers_size_pre = numbers_size0) |] 
  &&  [| (0 <= numbers_size0) |] 
  &&  [| (numbers_size0 < INT_MAX) |] 
  &&  [| (problem_8_pre ) |] 
  &&  [| (list_int_range lv ) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
.

Definition sum_product_partial_solve_wit_1 := sum_product_partial_solve_wit_1_pure -> sum_product_partial_solve_wit_1_aux.

Definition sum_product_partial_solve_wit_2 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
|--
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (((numbers0 + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers0 i 0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
.

Definition sum_product_partial_solve_wit_3 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
|--
  [| (i < numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (((numbers0 + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers0 i 0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
.

Definition sum_product_partial_solve_wit_4 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i >= numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.undef_full out 2 )
|--
  [| (i >= numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (((out + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out 1 2 )
  **  (IntArray.full numbers0 numbers_size0 lv )
.

Definition sum_product_partial_solve_wit_5 := 
forall (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (product: Z) (sum: Z) (i: Z) (out: Z) ,
  [| (i >= numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (((out + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.undef_seg out 1 2 )
  **  (IntArray.full numbers0 numbers_size0 lv )
|--
  [| (i >= numbers_size0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size0) |] 
  &&  [| (sum = (prefix_sum (lv) (i))) |] 
  &&  [| (product = (prefix_product (lv) (i))) |] 
  &&  [| (prefix_sum_product_int_range lv numbers_size0 ) |]
  &&  (((out + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((out + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.full numbers0 numbers_size0 lv )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_sum_product_safety_wit_1 : sum_product_safety_wit_1.
Axiom proof_of_sum_product_safety_wit_2 : sum_product_safety_wit_2.
Axiom proof_of_sum_product_safety_wit_3 : sum_product_safety_wit_3.
Axiom proof_of_sum_product_safety_wit_4 : sum_product_safety_wit_4.
Axiom proof_of_sum_product_safety_wit_5 : sum_product_safety_wit_5.
Axiom proof_of_sum_product_safety_wit_6 : sum_product_safety_wit_6.
Axiom proof_of_sum_product_safety_wit_7 : sum_product_safety_wit_7.
Axiom proof_of_sum_product_safety_wit_8 : sum_product_safety_wit_8.
Axiom proof_of_sum_product_safety_wit_9 : sum_product_safety_wit_9.
Axiom proof_of_sum_product_entail_wit_1 : sum_product_entail_wit_1.
Axiom proof_of_sum_product_entail_wit_2 : sum_product_entail_wit_2.
Axiom proof_of_sum_product_return_wit_1 : sum_product_return_wit_1.
Axiom proof_of_sum_product_partial_solve_wit_1_pure : sum_product_partial_solve_wit_1_pure.
Axiom proof_of_sum_product_partial_solve_wit_1 : sum_product_partial_solve_wit_1.
Axiom proof_of_sum_product_partial_solve_wit_2 : sum_product_partial_solve_wit_2.
Axiom proof_of_sum_product_partial_solve_wit_3 : sum_product_partial_solve_wit_3.
Axiom proof_of_sum_product_partial_solve_wit_4 : sum_product_partial_solve_wit_4.
Axiom proof_of_sum_product_partial_solve_wit_5 : sum_product_partial_solve_wit_5.

End VC_Correct.
