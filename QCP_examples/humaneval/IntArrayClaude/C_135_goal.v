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
Require Import coins_135.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function can_arrange -----*)

Definition can_arrange_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |]
  &&  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition can_arrange_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |]
  &&  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition can_arrange_safety_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition can_arrange_safety_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (max: Z) (i: Z) ,
  [| ((Znth i input_l 0) > i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix i input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition can_arrange_safety_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (max: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix i input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition can_arrange_entail_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix 0 input_l (-1) ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition can_arrange_entail_wit_2_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (max: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix i input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix (i + 1 ) input_l i ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition can_arrange_entail_wit_2_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (max: Z) (i: Z) ,
  [| ((Znth i input_l 0) > i) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix i input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix (i + 1 ) input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition can_arrange_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (max: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix i input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (problem_135_spec_z input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition can_arrange_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (max: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix i input_l max ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_135_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (can_arrange_prefix i input_l max ) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_can_arrange_safety_wit_1 : can_arrange_safety_wit_1.
Axiom proof_of_can_arrange_safety_wit_2 : can_arrange_safety_wit_2.
Axiom proof_of_can_arrange_safety_wit_3 : can_arrange_safety_wit_3.
Axiom proof_of_can_arrange_safety_wit_4 : can_arrange_safety_wit_4.
Axiom proof_of_can_arrange_safety_wit_5 : can_arrange_safety_wit_5.
Axiom proof_of_can_arrange_entail_wit_1 : can_arrange_entail_wit_1.
Axiom proof_of_can_arrange_entail_wit_2_1 : can_arrange_entail_wit_2_1.
Axiom proof_of_can_arrange_entail_wit_2_2 : can_arrange_entail_wit_2_2.
Axiom proof_of_can_arrange_return_wit_1 : can_arrange_return_wit_1.
Axiom proof_of_can_arrange_partial_solve_wit_1 : can_arrange_partial_solve_wit_1.

End VC_Correct.
