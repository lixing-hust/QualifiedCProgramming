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
Require Import coins_40.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function triples_sum_to_zero -----*)

Definition triples_sum_to_zero_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (problem_40_pre input_l ) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition triples_sum_to_zero_safety_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition triples_sum_to_zero_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition triples_sum_to_zero_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition triples_sum_to_zero_safety_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition triples_sum_to_zero_safety_wit_6 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  [| ((((Znth i input_l 0) + (Znth j input_l 0) ) + (Znth k input_l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i input_l 0) + (Znth j input_l 0) ) + (Znth k input_l 0) )) |]
.

Definition triples_sum_to_zero_safety_wit_7 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  [| (((Znth i input_l 0) + (Znth j input_l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i input_l 0) + (Znth j input_l 0) )) |]
.

Definition triples_sum_to_zero_safety_wit_8 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition triples_sum_to_zero_safety_wit_9 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| ((((Znth i input_l 0) + (Znth j input_l 0) ) + (Znth k input_l 0) ) = 0) |] 
  &&  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition triples_sum_to_zero_safety_wit_10 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition triples_sum_to_zero_safety_wit_11 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| ((((Znth i input_l 0) + (Znth j input_l 0) ) + (Znth k input_l 0) ) <> 0) |] 
  &&  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition triples_sum_to_zero_safety_wit_12 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition triples_sum_to_zero_safety_wit_13 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition triples_sum_to_zero_entail_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (problem_40_pre input_l ) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre 0 ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition triples_sum_to_zero_entail_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i (i + 1 ) ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition triples_sum_to_zero_entail_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j (j + 1 ) ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition triples_sum_to_zero_entail_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i (j + 1 ) ) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition triples_sum_to_zero_entail_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| ((((Znth i input_l 0) + (Znth j input_l 0) ) + (Znth k input_l 0) ) <> 0) |] 
  &&  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j (k + 1 ) ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition triples_sum_to_zero_entail_wit_6 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (j: Z) (i: Z) ,
  [| (j >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_j input_l l_size_pre i j ) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre (i + 1 ) ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition triples_sum_to_zero_return_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_i input_l l_size_pre i ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  ([| (0 = 0) |] 
  &&  [| (problem_40_spec input_l false ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
  ||
  ([| (0 <> 0) |] 
  &&  [| (problem_40_spec input_l true ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
.

Definition triples_sum_to_zero_return_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| ((((Znth i input_l 0) + (Znth j input_l 0) ) + (Znth k input_l 0) ) = 0) |] 
  &&  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  ([| (1 = 0) |] 
  &&  [| (problem_40_spec input_l false ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
  ||
  ([| (1 <> 0) |] 
  &&  [| (problem_40_spec input_l true ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
.

Definition triples_sum_to_zero_partial_solve_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
.

Definition triples_sum_to_zero_partial_solve_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (((l_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j input_l 0))
  **  (IntArray.missing_i l_pre j 0 l_size_pre input_l )
.

Definition triples_sum_to_zero_partial_solve_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (k < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < j) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| ((j + 1 ) <= k) |] 
  &&  [| (k <= l_size_pre) |] 
  &&  [| (triple_sum_int_range input_l l_size_pre ) |] 
  &&  [| (scanned_k input_l l_size_pre i j k ) |]
  &&  (((l_pre + (k * sizeof(INT) ) )) # Int  |-> (Znth k input_l 0))
  **  (IntArray.missing_i l_pre k 0 l_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_triples_sum_to_zero_safety_wit_1 : triples_sum_to_zero_safety_wit_1.
Axiom proof_of_triples_sum_to_zero_safety_wit_2 : triples_sum_to_zero_safety_wit_2.
Axiom proof_of_triples_sum_to_zero_safety_wit_3 : triples_sum_to_zero_safety_wit_3.
Axiom proof_of_triples_sum_to_zero_safety_wit_4 : triples_sum_to_zero_safety_wit_4.
Axiom proof_of_triples_sum_to_zero_safety_wit_5 : triples_sum_to_zero_safety_wit_5.
Axiom proof_of_triples_sum_to_zero_safety_wit_6 : triples_sum_to_zero_safety_wit_6.
Axiom proof_of_triples_sum_to_zero_safety_wit_7 : triples_sum_to_zero_safety_wit_7.
Axiom proof_of_triples_sum_to_zero_safety_wit_8 : triples_sum_to_zero_safety_wit_8.
Axiom proof_of_triples_sum_to_zero_safety_wit_9 : triples_sum_to_zero_safety_wit_9.
Axiom proof_of_triples_sum_to_zero_safety_wit_10 : triples_sum_to_zero_safety_wit_10.
Axiom proof_of_triples_sum_to_zero_safety_wit_11 : triples_sum_to_zero_safety_wit_11.
Axiom proof_of_triples_sum_to_zero_safety_wit_12 : triples_sum_to_zero_safety_wit_12.
Axiom proof_of_triples_sum_to_zero_safety_wit_13 : triples_sum_to_zero_safety_wit_13.
Axiom proof_of_triples_sum_to_zero_entail_wit_1 : triples_sum_to_zero_entail_wit_1.
Axiom proof_of_triples_sum_to_zero_entail_wit_2 : triples_sum_to_zero_entail_wit_2.
Axiom proof_of_triples_sum_to_zero_entail_wit_3 : triples_sum_to_zero_entail_wit_3.
Axiom proof_of_triples_sum_to_zero_entail_wit_4 : triples_sum_to_zero_entail_wit_4.
Axiom proof_of_triples_sum_to_zero_entail_wit_5 : triples_sum_to_zero_entail_wit_5.
Axiom proof_of_triples_sum_to_zero_entail_wit_6 : triples_sum_to_zero_entail_wit_6.
Axiom proof_of_triples_sum_to_zero_return_wit_1 : triples_sum_to_zero_return_wit_1.
Axiom proof_of_triples_sum_to_zero_return_wit_2 : triples_sum_to_zero_return_wit_2.
Axiom proof_of_triples_sum_to_zero_partial_solve_wit_1 : triples_sum_to_zero_partial_solve_wit_1.
Axiom proof_of_triples_sum_to_zero_partial_solve_wit_2 : triples_sum_to_zero_partial_solve_wit_2.
Axiom proof_of_triples_sum_to_zero_partial_solve_wit_3 : triples_sum_to_zero_partial_solve_wit_3.

End VC_Correct.
