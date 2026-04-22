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
Require Import coins_43.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function pairs_sum_to_zero -----*)

Definition pairs_sum_to_zero_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (problem_43_pre input_l ) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pairs_sum_to_zero_safety_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pairs_sum_to_zero_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pairs_sum_to_zero_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| (((Znth i input_l 0) + (Znth j input_l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i input_l 0) + (Znth j input_l 0) )) |]
.

Definition pairs_sum_to_zero_safety_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pairs_sum_to_zero_safety_wit_6 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (((Znth i input_l 0) + (Znth j input_l 0) ) = 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pairs_sum_to_zero_safety_wit_7 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pairs_sum_to_zero_safety_wit_8 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (((Znth i input_l 0) + (Znth j input_l 0) ) <> 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition pairs_sum_to_zero_safety_wit_9 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pairs_sum_to_zero_entail_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (problem_43_pre input_l ) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre 0 ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition pairs_sum_to_zero_entail_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i (i + 1 ) ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition pairs_sum_to_zero_entail_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre (i + 1 ) ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition pairs_sum_to_zero_entail_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (((Znth i input_l 0) + (Znth j input_l 0) ) <> 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i (j + 1 ) ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition pairs_sum_to_zero_return_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  ([| (0 = 0) |] 
  &&  [| (problem_43_spec input_l false ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
  ||
  ([| (0 <> 0) |] 
  &&  [| (problem_43_spec input_l true ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
.

Definition pairs_sum_to_zero_return_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (((Znth i input_l 0) + (Znth j input_l 0) ) = 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  ([| (1 = 0) |] 
  &&  [| (problem_43_spec input_l false ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
  ||
  ([| (1 <> 0) |] 
  &&  [| (problem_43_spec input_l true ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
.

Definition pairs_sum_to_zero_partial_solve_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
.

Definition pairs_sum_to_zero_partial_solve_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (pair_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (((l_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j input_l 0))
  **  (IntArray.missing_i l_pre j 0 l_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_pairs_sum_to_zero_safety_wit_1 : pairs_sum_to_zero_safety_wit_1.
Axiom proof_of_pairs_sum_to_zero_safety_wit_2 : pairs_sum_to_zero_safety_wit_2.
Axiom proof_of_pairs_sum_to_zero_safety_wit_3 : pairs_sum_to_zero_safety_wit_3.
Axiom proof_of_pairs_sum_to_zero_safety_wit_4 : pairs_sum_to_zero_safety_wit_4.
Axiom proof_of_pairs_sum_to_zero_safety_wit_5 : pairs_sum_to_zero_safety_wit_5.
Axiom proof_of_pairs_sum_to_zero_safety_wit_6 : pairs_sum_to_zero_safety_wit_6.
Axiom proof_of_pairs_sum_to_zero_safety_wit_7 : pairs_sum_to_zero_safety_wit_7.
Axiom proof_of_pairs_sum_to_zero_safety_wit_8 : pairs_sum_to_zero_safety_wit_8.
Axiom proof_of_pairs_sum_to_zero_safety_wit_9 : pairs_sum_to_zero_safety_wit_9.
Axiom proof_of_pairs_sum_to_zero_entail_wit_1 : pairs_sum_to_zero_entail_wit_1.
Axiom proof_of_pairs_sum_to_zero_entail_wit_2 : pairs_sum_to_zero_entail_wit_2.
Axiom proof_of_pairs_sum_to_zero_entail_wit_3 : pairs_sum_to_zero_entail_wit_3.
Axiom proof_of_pairs_sum_to_zero_entail_wit_4 : pairs_sum_to_zero_entail_wit_4.
Axiom proof_of_pairs_sum_to_zero_return_wit_1 : pairs_sum_to_zero_return_wit_1.
Axiom proof_of_pairs_sum_to_zero_return_wit_2 : pairs_sum_to_zero_return_wit_2.
Axiom proof_of_pairs_sum_to_zero_partial_solve_wit_1 : pairs_sum_to_zero_partial_solve_wit_1.
Axiom proof_of_pairs_sum_to_zero_partial_solve_wit_2 : pairs_sum_to_zero_partial_solve_wit_2.

End VC_Correct.
