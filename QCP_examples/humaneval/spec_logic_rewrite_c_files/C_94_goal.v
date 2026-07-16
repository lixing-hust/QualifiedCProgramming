Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_94.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function skjkasdkd -----*)

Definition skjkasdkd_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "largest" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "prime" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "prime" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "original" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "prime" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  ((( &( "original" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "prime" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "largest" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x > largest)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (INT_MIN <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest <= 2147395599)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (INT_MIN <= prime)) (PreH16 : (prime <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (INT_MIN <= sum)) (PreH20 : (sum <= INT_MAX)) (PreH21 : (INT_MIN <= original)) (PreH22 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition skjkasdkd_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x > 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition skjkasdkd_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x > 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "prime" ) )) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition skjkasdkd_safety_wit_12 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : (2 <= j)) (PreH15 : (j <= x)) (PreH16 : (j <= 46340)) (PreH17 : (0 <= prime)) (PreH18 : (prime <= 1)) (PreH19 : (prime_scan_state_94 x j prime )) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((j * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j * j )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : (2 <= j)) (PreH15 : (j <= x)) (PreH16 : (j <= 46340)) (PreH17 : (0 <= prime)) (PreH18 : (prime <= 1)) (PreH19 : (prime_scan_state_94 x j prime )) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((j * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j * j )) ”
).

Definition skjkasdkd_safety_wit_12_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : (2 <= j)) (PreH15 : (j <= x)) (PreH16 : (j <= 46340)) (PreH17 : (0 <= prime)) (PreH18 : (prime <= 1)) (PreH19 : (prime_scan_state_94 x j prime )) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((j * j ) <= INT_MAX) ”
.

Definition skjkasdkd_safety_wit_12_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : (2 <= j)) (PreH15 : (j <= x)) (PreH16 : (j <= 46340)) (PreH17 : (0 <= prime)) (PreH18 : (prime <= 1)) (PreH19 : (prime_scan_state_94 x j prime )) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((INT_MIN) <= (j * j )) ”
.

Definition skjkasdkd_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((j * j ) <= x)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x j prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((x <> (INT_MIN)) \/ (j <> (-1))) ” 
  &&  “ (j <> 0) ”
.

Definition skjkasdkd_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((j * j ) <= x)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x j prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) = 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : ((j * j ) <= x)) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j < 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x (j + 1 ) prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition skjkasdkd_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : (2 <= j)) (PreH15 : (j <= x)) (PreH16 : (j <= 46340)) (PreH17 : ((j * j ) > x)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_flag_done_94 x j prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition skjkasdkd_safety_wit_18 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (INT_MIN <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= 2147395599)) (PreH13 : (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l)))) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition skjkasdkd_safety_wit_19 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "original" ) )) # Int  |-> largest)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_20 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (i = lst_size_pre)) (PreH7 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH8 : (0 <= original)) (PreH9 : (original <= 2147395599)) (PreH10 : (0 <= largest)) (PreH11 : (largest <= original)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= INT_MAX)) (PreH14 : (digit_sum_state_94 original largest sum )) (PreH15 : (INT_MIN <= i)) (PreH16 : (i <= INT_MAX)) (PreH17 : (INT_MIN <= x)) (PreH18 : (x <= INT_MAX)) (PreH19 : (INT_MIN <= prime)) (PreH20 : (prime <= INT_MAX)) (PreH21 : (INT_MIN <= j)) (PreH22 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition skjkasdkd_safety_wit_21 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((sum + (largest % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (largest % ( 10 ) ) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((sum + (largest % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (largest % ( 10 ) ) )) ”
).

Definition skjkasdkd_safety_wit_21_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((sum + (largest % ( 10 ) ) ) <= INT_MAX) ”
.

Definition skjkasdkd_safety_wit_21_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((INT_MIN) <= (sum + (largest % ( 10 ) ) )) ”
.

Definition skjkasdkd_safety_wit_22 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((largest <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition skjkasdkd_safety_wit_23 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition skjkasdkd_safety_wit_24 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (largest % ( 10 ) ) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((largest <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition skjkasdkd_safety_wit_25 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "original" ) )) # Int  |-> original)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (largest % ( 10 ) ) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition skjkasdkd_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2147395599) ” 
  &&  “ (0 = (largest_prime_prefix_94 (0) (input_l))) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  TT && emp 
|--
  “ (0 = (largest_prime_prefix_94 (0) (input_l))) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) ,
  TT && emp 
|--
  “ (0 = (largest_prime_prefix_94 (0) (input_l))) ”
.

Definition skjkasdkd_entail_wit_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= 2147395599) ” 
  &&  “ (largest = (largest_prime_prefix_94 (i) (input_l))) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) <= 2147395599) ” 
  &&  “ (INT_MIN <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) <= 2147395599) ”
.

Definition skjkasdkd_entail_wit_2_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN <= (Znth i input_l 0)) ”
.

Definition skjkasdkd_entail_wit_2_split_goal_3 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
.

Definition skjkasdkd_entail_wit_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x > 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (2 <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < x) ” 
  &&  “ (largest = (largest_prime_prefix_94 (i) (input_l))) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= x) ” 
  &&  “ (2 <= 46340) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (prime_scan_state_94 x 2 1 ) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x > 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_scan_state_94 x 2 1 ) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_3_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x > 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_scan_state_94 x 2 1 ) ”
.

Definition skjkasdkd_entail_wit_4_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) <> 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (2 <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < x) ” 
  &&  “ (largest = (largest_prime_prefix_94 (i) (input_l))) ” 
  &&  “ ((j * j ) <= x) ” 
  &&  “ (2 <= j) ” 
  &&  “ (j <= x) ” 
  &&  “ (j < 46340) ” 
  &&  “ (0 <= prime) ” 
  &&  “ (prime <= 1) ” 
  &&  “ (prime_scan_state_94 x (j + 1 ) prime ) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) <> 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_scan_state_94 x (j + 1 ) prime ) ” 
  &&  “ (j < 46340) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_4_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) <> 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_scan_state_94 x (j + 1 ) prime ) ”
.

Definition skjkasdkd_entail_wit_4_1_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) <> 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (j < 46340) ”
.

Definition skjkasdkd_entail_wit_4_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) = 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (2 <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < x) ” 
  &&  “ (largest = (largest_prime_prefix_94 (i) (input_l))) ” 
  &&  “ ((j * j ) <= x) ” 
  &&  “ (2 <= j) ” 
  &&  “ (j <= x) ” 
  &&  “ (j < 46340) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (prime_scan_state_94 x (j + 1 ) 0 ) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) = 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_scan_state_94 x (j + 1 ) 0 ) ” 
  &&  “ (j < 46340) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_4_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) = 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_scan_state_94 x (j + 1 ) 0 ) ”
.

Definition skjkasdkd_entail_wit_4_2_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((x % ( j ) ) = 0)) (PreH2 : ((j * j ) <= x)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (2 <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest < x)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (2 <= j)) (PreH17 : (j <= x)) (PreH18 : (j <= 46340)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_scan_state_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (j < 46340) ”
.

Definition skjkasdkd_entail_wit_5 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : ((j * j ) <= x)) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j < 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x (j + 1 ) prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (2 <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < x) ” 
  &&  “ (largest = (largest_prime_prefix_94 (i) (input_l))) ” 
  &&  “ (2 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= x) ” 
  &&  “ ((j + 1 ) <= 46340) ” 
  &&  “ (0 <= prime) ” 
  &&  “ (prime <= 1) ” 
  &&  “ (prime_scan_state_94 x (j + 1 ) prime ) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : ((j * j ) <= x)) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j < 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x (j + 1 ) prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ ((j + 1 ) <= x) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_5_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (2 <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest < x)) (PreH13 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH14 : ((j * j ) <= x)) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j < 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x (j + 1 ) prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ ((j + 1 ) <= x) ”
.

Definition skjkasdkd_entail_wit_6 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((j * j ) > x)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x j prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (2 <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < x) ” 
  &&  “ (largest = (largest_prime_prefix_94 (i) (input_l))) ” 
  &&  “ (2 <= j) ” 
  &&  “ (j <= x) ” 
  &&  “ (j <= 46340) ” 
  &&  “ ((j * j ) > x) ” 
  &&  “ (0 <= prime) ” 
  &&  “ (prime <= 1) ” 
  &&  “ (prime_flag_done_94 x j prime ) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((j * j ) > x)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x j prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_flag_done_94 x j prime ) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_6_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (prime: Z) (j: Z) (largest: Z) (x: Z) (i: Z) (PreH1 : ((j * j ) > x)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : (0 <= prime)) (PreH19 : (prime <= 1)) (PreH20 : (prime_scan_state_94 x j prime )) (PreH21 : (INT_MIN <= sum)) (PreH22 : (sum <= INT_MAX)) (PreH23 : (INT_MIN <= original)) (PreH24 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (prime_flag_done_94 x j prime ) ”
.

Definition skjkasdkd_entail_wit_7_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x <= 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= 2147395599) ” 
  &&  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x <= 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_7_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x <= 1)) (PreH2 : (x > largest)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_94_pre_z input_l )) (PreH7 : (skjkasdkd_safe_94 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= x)) (PreH12 : (x <= 2147395599)) (PreH13 : (0 <= largest)) (PreH14 : (largest <= 2147395599)) (PreH15 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH16 : (INT_MIN <= prime)) (PreH17 : (prime <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : (INT_MIN <= sum)) (PreH21 : (sum <= INT_MAX)) (PreH22 : (INT_MIN <= original)) (PreH23 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
.

Definition skjkasdkd_entail_wit_7_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x <= largest)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (INT_MIN <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest <= 2147395599)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (INT_MIN <= prime)) (PreH16 : (prime <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (INT_MIN <= sum)) (PreH20 : (sum <= INT_MAX)) (PreH21 : (INT_MIN <= original)) (PreH22 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= 2147395599) ” 
  &&  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x <= largest)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (INT_MIN <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest <= 2147395599)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (INT_MIN <= prime)) (PreH16 : (prime <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (INT_MIN <= sum)) (PreH20 : (sum <= INT_MAX)) (PreH21 : (INT_MIN <= original)) (PreH22 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_7_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (x <= largest)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (INT_MIN <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest <= 2147395599)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (INT_MIN <= prime)) (PreH16 : (prime <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (INT_MIN <= sum)) (PreH20 : (sum <= INT_MAX)) (PreH21 : (INT_MIN <= original)) (PreH22 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
.

Definition skjkasdkd_entail_wit_7_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (prime <> 1)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : ((j * j ) > x)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_flag_done_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= 2147395599) ” 
  &&  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (prime <> 1)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : ((j * j ) > x)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_flag_done_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_7_3_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (prime <> 1)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : ((j * j ) > x)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_flag_done_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
.

Definition skjkasdkd_entail_wit_7_4 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (prime = 1)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : ((j * j ) > x)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_flag_done_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x <= 2147395599) ” 
  &&  “ (x = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (prime = 1)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : ((j * j ) > x)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_flag_done_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (x = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_7_4_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (j: Z) (prime: Z) (sum: Z) (original: Z) (PreH1 : (prime = 1)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (2 <= x)) (PreH11 : (x <= 2147395599)) (PreH12 : (0 <= largest)) (PreH13 : (largest < x)) (PreH14 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH15 : (2 <= j)) (PreH16 : (j <= x)) (PreH17 : (j <= 46340)) (PreH18 : ((j * j ) > x)) (PreH19 : (0 <= prime)) (PreH20 : (prime <= 1)) (PreH21 : (prime_flag_done_94 x j prime )) (PreH22 : (INT_MIN <= sum)) (PreH23 : (sum <= INT_MAX)) (PreH24 : (INT_MIN <= original)) (PreH25 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (x = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ”
.

Definition skjkasdkd_entail_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (largest: Z) (prime: Z) (j: Z) (sum: Z) (original: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (INT_MIN <= x)) (PreH10 : (x <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= 2147395599)) (PreH13 : (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l)))) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= 2147395599) ” 
  &&  “ (largest = (largest_prime_prefix_94 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition skjkasdkd_entail_wit_9 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (i = lst_size_pre) ” 
  &&  “ (largest = (largest_prime_prefix_94 (lst_size_pre) (input_l))) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= largest) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (digit_sum_state_94 largest largest 0 ) ” 
  &&  “ (INT_MIN <= i) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit_sum_state_94 largest largest 0 ) ” 
  &&  “ (largest = (largest_prime_prefix_94 (lst_size_pre) (input_l))) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_9_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit_sum_state_94 largest largest 0 ) ”
.

Definition skjkasdkd_entail_wit_9_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  TT && emp 
|--
  “ (largest = (largest_prime_prefix_94 (lst_size_pre) (input_l))) ”
.

Definition skjkasdkd_entail_wit_10 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (i = lst_size_pre) ” 
  &&  “ (original = (largest_prime_prefix_94 (lst_size_pre) (input_l))) ” 
  &&  “ (0 <= original) ” 
  &&  “ (original <= 2147395599) ” 
  &&  “ (0 <= (largest ÷ 10 )) ” 
  &&  “ ((largest ÷ 10 ) <= original) ” 
  &&  “ (0 <= (sum + (largest % ( 10 ) ) )) ” 
  &&  “ ((sum + (largest % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (digit_sum_state_94 original (largest ÷ 10 ) (sum + (largest % ( 10 ) ) ) ) ” 
  &&  “ (INT_MIN <= i) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit_sum_state_94 original (largest ÷ 10 ) (sum + (largest % ( 10 ) ) ) ) ” 
  &&  “ ((sum + (largest % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (0 <= (sum + (largest % ( 10 ) ) )) ” 
  &&  “ ((largest ÷ 10 ) <= original) ” 
  &&  “ (0 <= (largest ÷ 10 )) ”
  &&  emp
).

Definition skjkasdkd_entail_wit_10_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit_sum_state_94 original (largest ÷ 10 ) (sum + (largest % ( 10 ) ) ) ) ”
.

Definition skjkasdkd_entail_wit_10_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (largest % ( 10 ) ) ) <= INT_MAX) ”
.

Definition skjkasdkd_entail_wit_10_split_goal_3 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (sum + (largest % ( 10 ) ) )) ”
.

Definition skjkasdkd_entail_wit_10_split_goal_4 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ ((largest ÷ 10 ) <= original) ”
.

Definition skjkasdkd_entail_wit_10_split_goal_5 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest > 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (largest ÷ 10 )) ”
.

Definition skjkasdkd_entail_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (original: Z) (largest: Z) (sum: Z) (x: Z) (prime: Z) (j: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_94_pre_z input_l )) (PreH5 : (skjkasdkd_safe_94 input_l )) (PreH6 : (i = lst_size_pre)) (PreH7 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH8 : (0 <= original)) (PreH9 : (original <= 2147395599)) (PreH10 : (0 <= largest)) (PreH11 : (largest <= original)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= INT_MAX)) (PreH14 : (digit_sum_state_94 original largest sum )) (PreH15 : (INT_MIN <= i)) (PreH16 : (i <= INT_MAX)) (PreH17 : (INT_MIN <= x)) (PreH18 : (x <= INT_MAX)) (PreH19 : (INT_MIN <= prime)) (PreH20 : (prime <= INT_MAX)) (PreH21 : (INT_MIN <= j)) (PreH22 : (j <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (i = lst_size_pre) ” 
  &&  “ (original = (largest_prime_prefix_94 (lst_size_pre) (input_l))) ” 
  &&  “ (0 <= original) ” 
  &&  “ (original <= 2147395599) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= original) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (digit_sum_state_94 original largest sum ) ” 
  &&  “ (INT_MIN <= i) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition skjkasdkd_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest <= 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (problem_94_spec_z input_l sum ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest <= 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_94_spec_z input_l sum ) ”
  &&  emp
).

Definition skjkasdkd_return_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (j: Z) (prime: Z) (x: Z) (sum: Z) (largest: Z) (original: Z) (i: Z) (PreH1 : (largest <= 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (i = lst_size_pre)) (PreH8 : (original = (largest_prime_prefix_94 (lst_size_pre) (input_l)))) (PreH9 : (0 <= original)) (PreH10 : (original <= 2147395599)) (PreH11 : (0 <= largest)) (PreH12 : (largest <= original)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= INT_MAX)) (PreH15 : (digit_sum_state_94 original largest sum )) (PreH16 : (INT_MIN <= i)) (PreH17 : (i <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= prime)) (PreH21 : (prime <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_94_spec_z input_l sum ) ”
.

Definition skjkasdkd_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (original: Z) (sum: Z) (j: Z) (prime: Z) (x: Z) (largest: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_94_pre_z input_l )) (PreH6 : (skjkasdkd_safe_94 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (0 <= largest)) (PreH10 : (largest <= 2147395599)) (PreH11 : (largest = (largest_prime_prefix_94 (i) (input_l)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= prime)) (PreH15 : (prime <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= sum)) (PreH19 : (sum <= INT_MAX)) (PreH20 : (INT_MIN <= original)) (PreH21 : (original <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_94_pre_z input_l ) ” 
  &&  “ (skjkasdkd_safe_94 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest <= 2147395599) ” 
  &&  “ (largest = (largest_prime_prefix_94 (i) (input_l))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= prime) ” 
  &&  “ (prime <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (INT_MIN <= original) ” 
  &&  “ (original <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
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
Axiom proof_of_skjkasdkd_entail_wit_3 : skjkasdkd_entail_wit_3.
Axiom proof_of_skjkasdkd_entail_wit_4_1 : skjkasdkd_entail_wit_4_1.
Axiom proof_of_skjkasdkd_entail_wit_4_2 : skjkasdkd_entail_wit_4_2.
Axiom proof_of_skjkasdkd_entail_wit_5 : skjkasdkd_entail_wit_5.
Axiom proof_of_skjkasdkd_entail_wit_6 : skjkasdkd_entail_wit_6.
Axiom proof_of_skjkasdkd_entail_wit_7_1 : skjkasdkd_entail_wit_7_1.
Axiom proof_of_skjkasdkd_entail_wit_7_2 : skjkasdkd_entail_wit_7_2.
Axiom proof_of_skjkasdkd_entail_wit_7_3 : skjkasdkd_entail_wit_7_3.
Axiom proof_of_skjkasdkd_entail_wit_7_4 : skjkasdkd_entail_wit_7_4.
Axiom proof_of_skjkasdkd_entail_wit_8 : skjkasdkd_entail_wit_8.
Axiom proof_of_skjkasdkd_entail_wit_9 : skjkasdkd_entail_wit_9.
Axiom proof_of_skjkasdkd_entail_wit_10 : skjkasdkd_entail_wit_10.
Axiom proof_of_skjkasdkd_entail_wit_11 : skjkasdkd_entail_wit_11.
Axiom proof_of_skjkasdkd_return_wit_1 : skjkasdkd_return_wit_1.
Axiom proof_of_skjkasdkd_partial_solve_wit_1 : skjkasdkd_partial_solve_wit_1.

End VC_Correct.
