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

(*----- Function smallest_change -----*)

Definition smallest_change_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition smallest_change_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition smallest_change_safety_wit_3 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (((arr_size_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((arr_size_pre - 1 ) - i )) |]
.

Definition smallest_change_safety_wit_4 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((arr_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (arr_size_pre - 1 )) |]
.

Definition smallest_change_safety_wit_5 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition smallest_change_safety_wit_6 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (((arr_size_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((arr_size_pre - 1 ) - i )) |]
.

Definition smallest_change_safety_wit_7 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((arr_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (arr_size_pre - 1 )) |]
.

Definition smallest_change_safety_wit_8 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition smallest_change_safety_wit_9 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((arr_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition smallest_change_safety_wit_10 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((arr_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition smallest_change_safety_wit_11 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((arr_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition smallest_change_safety_wit_12 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((arr_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition smallest_change_entail_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (0 <= 0) |] 
  &&  [| ((2 * 0 ) <= arr_size_pre) |] 
  &&  [| (0 = (count_half_mismatches_upto (0) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition smallest_change_entail_wit_2_1 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((arr_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((2 * (i + 1 ) ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto ((i + 1 )) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
.

Definition smallest_change_entail_wit_2_2 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((arr_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((2 * (i + 1 ) ) <= arr_size_pre) |] 
  &&  [| ((out + 1 ) = (count_half_mismatches_upto ((i + 1 )) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
.

Definition smallest_change_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (i >= ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (out = (count_half_mismatches (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition smallest_change_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (((arr + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i arr i 0 arr_size_pre lv )
.

Definition smallest_change_partial_solve_wit_2 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (i: Z) ,
  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (i < ((arr_size_pre - 1 ) - i )) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= arr_size_pre) |] 
  &&  [| (out = (count_half_mismatches_upto (i) (lv))) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (((arr + (((arr_size_pre - 1 ) - i ) * sizeof(INT) ) )) # Int  |-> (Znth ((arr_size_pre - 1 ) - i ) lv 0))
  **  (IntArray.missing_i arr ((arr_size_pre - 1 ) - i ) 0 arr_size_pre lv )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_smallest_change_safety_wit_1 : smallest_change_safety_wit_1.
Axiom proof_of_smallest_change_safety_wit_2 : smallest_change_safety_wit_2.
Axiom proof_of_smallest_change_safety_wit_3 : smallest_change_safety_wit_3.
Axiom proof_of_smallest_change_safety_wit_4 : smallest_change_safety_wit_4.
Axiom proof_of_smallest_change_safety_wit_5 : smallest_change_safety_wit_5.
Axiom proof_of_smallest_change_safety_wit_6 : smallest_change_safety_wit_6.
Axiom proof_of_smallest_change_safety_wit_7 : smallest_change_safety_wit_7.
Axiom proof_of_smallest_change_safety_wit_8 : smallest_change_safety_wit_8.
Axiom proof_of_smallest_change_safety_wit_9 : smallest_change_safety_wit_9.
Axiom proof_of_smallest_change_safety_wit_10 : smallest_change_safety_wit_10.
Axiom proof_of_smallest_change_safety_wit_11 : smallest_change_safety_wit_11.
Axiom proof_of_smallest_change_safety_wit_12 : smallest_change_safety_wit_12.
Axiom proof_of_smallest_change_entail_wit_1 : smallest_change_entail_wit_1.
Axiom proof_of_smallest_change_entail_wit_2_1 : smallest_change_entail_wit_2_1.
Axiom proof_of_smallest_change_entail_wit_2_2 : smallest_change_entail_wit_2_2.
Axiom proof_of_smallest_change_return_wit_1 : smallest_change_return_wit_1.
Axiom proof_of_smallest_change_partial_solve_wit_1 : smallest_change_partial_solve_wit_1.
Axiom proof_of_smallest_change_partial_solve_wit_2 : smallest_change_partial_solve_wit_2.

End VC_Correct.
