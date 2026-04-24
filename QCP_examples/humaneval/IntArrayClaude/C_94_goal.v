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
Require Import coins_94.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function skjkasdkd -----*)

Definition skjkasdkd_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |]
  &&  ((( &( "largest" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition skjkasdkd_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition skjkasdkd_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition skjkasdkd_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) > 1) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  ((( &( "prime" ) )) # Int  |->_)
  **  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "x" ) )) # Int  |-> (Znth i lv 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition skjkasdkd_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) > 1) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> 1)
  **  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "x" ) )) # Int  |-> (Znth i lv 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition skjkasdkd_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (INT_MAX <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= INT_MAX) |]
.

Definition skjkasdkd_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((x <> (INT_MIN)) \/ (j <> (-1))) |] 
  &&  [| (j <> 0) |]
.

Definition skjkasdkd_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j <= (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((x <> (INT_MIN)) \/ (j <> (-1))) |] 
  &&  [| (j <> 0) |]
.

Definition skjkasdkd_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j <= (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition skjkasdkd_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| ((x % ( j ) ) = 0) |] 
  &&  [| (j <= (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition skjkasdkd_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| ((x % ( j ) ) <> 0) |] 
  &&  [| (j <= (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition skjkasdkd_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| ((x % ( j ) ) = 0) |] 
  &&  [| (j <= (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> 0)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition skjkasdkd_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) <= 1) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition skjkasdkd_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) <= largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition skjkasdkd_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j >= INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime = 0) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition skjkasdkd_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j > (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime = 0) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition skjkasdkd_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j > (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime <> 0) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> x)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition skjkasdkd_safety_wit_18 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j >= INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime <> 0) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> x)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition skjkasdkd_safety_wit_19 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition skjkasdkd_safety_wit_20 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest: Z) (i: Z) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest sum ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition skjkasdkd_safety_wit_21 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest: Z) (i: Z) ,
  [| (largest > 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest sum ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((sum + (largest % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (largest % ( 10 ) ) )) |]
.

Definition skjkasdkd_safety_wit_22 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest: Z) (i: Z) ,
  [| (largest > 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest sum ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((largest <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition skjkasdkd_safety_wit_23 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest: Z) (i: Z) ,
  [| (largest > 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest sum ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition skjkasdkd_safety_wit_24 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest: Z) (i: Z) ,
  [| (largest > 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest sum ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (largest % ( 10 ) ) ))
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((largest <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition skjkasdkd_safety_wit_25 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest: Z) (i: Z) ,
  [| (largest > 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest sum ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (largest % ( 10 ) ) ))
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition skjkasdkd_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix 0 lv 0 ) |] 
  &&  [| (digit_sum_int_range 0 ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) > 1) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| ((Znth i lv 0) = (Znth (i) (lv) (0))) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| ((Znth i lv 0) > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= ((Znth i lv 0) + 1 )) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (prime_scan_state (Znth i lv 0) 2 1 ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_3_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| ((x % ( j ) ) = 0) |] 
  &&  [| (j <= (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= (x + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (prime_scan_state x (j + 1 ) 0 ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_3_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| ((x % ( j ) ) <> 0) |] 
  &&  [| (j <= (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x (j + 1 ) prime ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_4_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j >= INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime <> 0) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix (i + 1 ) lv x ) |] 
  &&  [| (digit_sum_int_range x ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_4_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j > (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime <> 0) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix (i + 1 ) lv x ) |] 
  &&  [| (digit_sum_int_range x ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_4_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j > (x ÷ j )) |] 
  &&  [| (j < INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime = 0) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix (i + 1 ) lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_4_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) ,
  [| (j >= INT_MAX) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (x = (Znth (i) (lv) (0))) |] 
  &&  [| (x > largest) |] 
  &&  [| (x > 1) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= (x + 1 )) |] 
  &&  [| (0 <= prime) |] 
  &&  [| (prime <= 1) |] 
  &&  [| (prime_scan_state x j prime ) |] 
  &&  [| (prime = 0) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix (i + 1 ) lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_4_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) <= largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix (i + 1 ) lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_4_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) <= 1) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix (i + 1 ) lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  EX (original_largest: Z) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest 0 ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_entail_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest_2: Z) (i: Z) ,
  [| (largest > 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest_2 ) |] 
  &&  [| (digit_sum_int_range original_largest_2 ) |] 
  &&  [| (digit_sum_state original_largest_2 largest sum ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  EX (original_largest: Z) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest (largest ÷ 10 ) (sum + (largest % ( 10 ) ) ) ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (sum: Z) (original_largest: Z) (i: Z) ,
  [| (largest <= 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (i = lst_size_pre) |] 
  &&  [| (largest_prime_prefix lst_size_pre lv original_largest ) |] 
  &&  [| (digit_sum_int_range original_largest ) |] 
  &&  [| (digit_sum_state original_largest largest sum ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (problem_94_spec_z lv sum ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition skjkasdkd_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre lv )
.

Definition skjkasdkd_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre lv )
.

Definition skjkasdkd_partial_solve_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (largest: Z) (i: Z) ,
  [| ((Znth i lv 0) > 1) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((Znth i lv 0) > 1) |] 
  &&  [| ((Znth i lv 0) > largest) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_94_pre_z lv ) |] 
  &&  [| (list_nonneg_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_prime_prefix i lv largest ) |] 
  &&  [| (digit_sum_int_range largest ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_skjkasdkd_safety_wit_1 : skjkasdkd_safety_wit_1.
Axiom proof_of_skjkasdkd_safety_wit_2 : skjkasdkd_safety_wit_2.
Axiom proof_of_skjkasdkd_safety_wit_3 : skjkasdkd_safety_wit_3.
Axiom proof_of_skjkasdkd_safety_wit_4 : skjkasdkd_safety_wit_4.
Axiom proof_of_skjkasdkd_safety_wit_5 : skjkasdkd_safety_wit_5.
Axiom proof_of_skjkasdkd_safety_wit_6 : skjkasdkd_safety_wit_6.
Axiom proof_of_skjkasdkd_safety_wit_7 : skjkasdkd_safety_wit_7.
Axiom proof_of_skjkasdkd_safety_wit_8 : skjkasdkd_safety_wit_8.
Axiom proof_of_skjkasdkd_safety_wit_9 : skjkasdkd_safety_wit_9.
Axiom proof_of_skjkasdkd_safety_wit_10 : skjkasdkd_safety_wit_10.
Axiom proof_of_skjkasdkd_safety_wit_11 : skjkasdkd_safety_wit_11.
Axiom proof_of_skjkasdkd_safety_wit_12 : skjkasdkd_safety_wit_12.
Axiom proof_of_skjkasdkd_safety_wit_13 : skjkasdkd_safety_wit_13.
Axiom proof_of_skjkasdkd_safety_wit_14 : skjkasdkd_safety_wit_14.
Axiom proof_of_skjkasdkd_safety_wit_15 : skjkasdkd_safety_wit_15.
Axiom proof_of_skjkasdkd_safety_wit_16 : skjkasdkd_safety_wit_16.
Axiom proof_of_skjkasdkd_safety_wit_17 : skjkasdkd_safety_wit_17.
Axiom proof_of_skjkasdkd_safety_wit_18 : skjkasdkd_safety_wit_18.
Axiom proof_of_skjkasdkd_safety_wit_19 : skjkasdkd_safety_wit_19.
Axiom proof_of_skjkasdkd_safety_wit_20 : skjkasdkd_safety_wit_20.
Axiom proof_of_skjkasdkd_safety_wit_21 : skjkasdkd_safety_wit_21.
Axiom proof_of_skjkasdkd_safety_wit_22 : skjkasdkd_safety_wit_22.
Axiom proof_of_skjkasdkd_safety_wit_23 : skjkasdkd_safety_wit_23.
Axiom proof_of_skjkasdkd_safety_wit_24 : skjkasdkd_safety_wit_24.
Axiom proof_of_skjkasdkd_safety_wit_25 : skjkasdkd_safety_wit_25.
Axiom proof_of_skjkasdkd_entail_wit_1 : skjkasdkd_entail_wit_1.
Axiom proof_of_skjkasdkd_entail_wit_2 : skjkasdkd_entail_wit_2.
Axiom proof_of_skjkasdkd_entail_wit_3_1 : skjkasdkd_entail_wit_3_1.
Axiom proof_of_skjkasdkd_entail_wit_3_2 : skjkasdkd_entail_wit_3_2.
Axiom proof_of_skjkasdkd_entail_wit_4_1 : skjkasdkd_entail_wit_4_1.
Axiom proof_of_skjkasdkd_entail_wit_4_2 : skjkasdkd_entail_wit_4_2.
Axiom proof_of_skjkasdkd_entail_wit_4_3 : skjkasdkd_entail_wit_4_3.
Axiom proof_of_skjkasdkd_entail_wit_4_4 : skjkasdkd_entail_wit_4_4.
Axiom proof_of_skjkasdkd_entail_wit_4_5 : skjkasdkd_entail_wit_4_5.
Axiom proof_of_skjkasdkd_entail_wit_4_6 : skjkasdkd_entail_wit_4_6.
Axiom proof_of_skjkasdkd_entail_wit_5 : skjkasdkd_entail_wit_5.
Axiom proof_of_skjkasdkd_entail_wit_6 : skjkasdkd_entail_wit_6.
Axiom proof_of_skjkasdkd_return_wit_1 : skjkasdkd_return_wit_1.
Axiom proof_of_skjkasdkd_partial_solve_wit_1 : skjkasdkd_partial_solve_wit_1.
Axiom proof_of_skjkasdkd_partial_solve_wit_2 : skjkasdkd_partial_solve_wit_2.
Axiom proof_of_skjkasdkd_partial_solve_wit_3 : skjkasdkd_partial_solve_wit_3.

End VC_Correct.
