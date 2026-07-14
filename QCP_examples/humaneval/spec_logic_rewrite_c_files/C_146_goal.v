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
Require Import coins_146.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function specialFilter -----*)

Definition specialFilter_safety_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (PreH1 : (nums_pre <> 0)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) ,
  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition specialFilter_safety_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (PreH1 : (nums_pre <> 0)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition specialFilter_safety_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN <= current)) (PreH12 : (current <= INT_MAX)) (PreH13 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition specialFilter_safety_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> current)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((current <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition specialFilter_safety_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> current)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition specialFilter_safety_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (1 <= first)) (PreH15 : (first <= current)) (PreH16 : (last = (current % ( 10 ) ))) (PreH17 : (first_digit_state_146 current first )) (PreH18 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition specialFilter_safety_wit_7 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first >= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((first <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition specialFilter_safety_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first >= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition specialFilter_safety_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (1 <= first)) (PreH15 : (first < 10)) (PreH16 : (last = (current % ( 10 ) ))) (PreH17 : (first_digit_state_146 current first )) (PreH18 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((first <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition specialFilter_safety_wit_10 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (1 <= first)) (PreH15 : (first < 10)) (PreH16 : (last = (current % ( 10 ) ))) (PreH17 : (first_digit_state_146 current first )) (PreH18 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition specialFilter_safety_wit_11 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (1 <= first)) (PreH15 : (first < 10)) (PreH16 : (last = (current % ( 10 ) ))) (PreH17 : (first_digit_state_146 current first )) (PreH18 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition specialFilter_safety_wit_12 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((first % ( 2 ) ) = 1)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first < 10)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((last <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition specialFilter_safety_wit_13 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((first % ( 2 ) ) = 1)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first < 10)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition specialFilter_safety_wit_14 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((first % ( 2 ) ) = 1)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first < 10)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition specialFilter_safety_wit_15 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((last % ( 2 ) ) = 1)) (PreH2 : ((first % ( 2 ) ) = 1)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_146_pre_z input_l )) (PreH7 : (special_filter_safe_146 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < nums_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (current > 10)) (PreH14 : (INT_MIN <= current)) (PreH15 : (current <= INT_MAX)) (PreH16 : (1 <= first)) (PreH17 : (first < 10)) (PreH18 : (last = (current % ( 10 ) ))) (PreH19 : (first_digit_state_146 current first )) (PreH20 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((num + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num + 1 )) ”
.

Definition specialFilter_safety_wit_16 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((last % ( 2 ) ) = 1)) (PreH2 : ((first % ( 2 ) ) = 1)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_146_pre_z input_l )) (PreH7 : (special_filter_safe_146 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < nums_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (current > 10)) (PreH14 : (INT_MIN <= current)) (PreH15 : (current <= INT_MAX)) (PreH16 : (1 <= first)) (PreH17 : (first < 10)) (PreH18 : (last = (current % ( 10 ) ))) (PreH19 : (first_digit_state_146 current first )) (PreH20 : (special_filter_prefix_146 input_l i num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition specialFilter_safety_wit_17 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (first_digit_state_146 current first )) (PreH13 : (first < 10)) (PreH14 : (last = (current % ( 10 ) ))) (PreH15 : ((first % ( 2 ) ) = 1)) (PreH16 : ((last % ( 2 ) ) = 1)) (PreH17 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition specialFilter_safety_wit_18 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (first_digit_state_146 current first )) (PreH13 : (first < 10)) (PreH14 : (last = (current % ( 10 ) ))) (PreH15 : ((last % ( 2 ) ) <> 1)) (PreH16 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition specialFilter_safety_wit_19 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (first_digit_state_146 current first )) (PreH13 : (first < 10)) (PreH14 : (last = (current % ( 10 ) ))) (PreH15 : ((first % ( 2 ) ) <> 1)) (PreH16 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition specialFilter_safety_wit_20 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current <= 10)) (PreH12 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition specialFilter_entail_wit_1 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (PreH1 : (nums_pre <> 0)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (special_filter_prefix_146 input_l 0 0 ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
) \/
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (PreH1 : (nums_pre <> 0)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) ,
  TT && emp 
|--
  “ (special_filter_prefix_146 input_l 0 0 ) ”
  &&  emp
).

Definition specialFilter_entail_wit_1_split_goal_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (PreH1 : (nums_pre <> 0)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) ,
  TT && emp 
|--
  “ (special_filter_prefix_146 input_l 0 0 ) ”
.

Definition specialFilter_entail_wit_2 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (special_filter_prefix_146 input_l i num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
  &&  emp
).

Definition specialFilter_entail_wit_2_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) <= INT_MAX) ”
.

Definition specialFilter_entail_wit_2_split_goal_2 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (INT_MIN <= (Znth i input_l 0)) ”
.

Definition specialFilter_entail_wit_2_split_goal_3 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
.

Definition specialFilter_entail_wit_3 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (INT_MIN <= current) ” 
  &&  “ (current <= INT_MAX) ” 
  &&  “ (current = current) ” 
  &&  “ ((current % ( 10 ) ) = (current % ( 10 ) )) ” 
  &&  “ (first_digit_state_146 current current ) ” 
  &&  “ (special_filter_prefix_146 input_l i num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (first_digit_state_146 current current ) ”
  &&  emp
).

Definition specialFilter_entail_wit_3_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (first_digit_state_146 current current ) ”
.

Definition specialFilter_entail_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (first = current)) (PreH15 : (last = (current % ( 10 ) ))) (PreH16 : (first_digit_state_146 current first )) (PreH17 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (INT_MIN <= current) ” 
  &&  “ (current <= INT_MAX) ” 
  &&  “ (1 <= first) ” 
  &&  “ (first <= current) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ (first_digit_state_146 current first ) ” 
  &&  “ (special_filter_prefix_146 input_l i num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_5 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first >= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (INT_MIN <= current) ” 
  &&  “ (current <= INT_MAX) ” 
  &&  “ (1 <= (first ÷ 10 )) ” 
  &&  “ ((first ÷ 10 ) <= current) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ (first_digit_state_146 current (first ÷ 10 ) ) ” 
  &&  “ (special_filter_prefix_146 input_l i num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first >= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (first_digit_state_146 current (first ÷ 10 ) ) ” 
  &&  “ ((first ÷ 10 ) <= current) ” 
  &&  “ (1 <= (first ÷ 10 )) ”
  &&  emp
).

Definition specialFilter_entail_wit_5_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first >= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (first_digit_state_146 current (first ÷ 10 ) ) ”
.

Definition specialFilter_entail_wit_5_split_goal_2 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first >= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ ((first ÷ 10 ) <= current) ”
.

Definition specialFilter_entail_wit_5_split_goal_3 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first >= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (1 <= (first ÷ 10 )) ”
.

Definition specialFilter_entail_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (last: Z) (first: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (first < 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first <= current)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (INT_MIN <= current) ” 
  &&  “ (current <= INT_MAX) ” 
  &&  “ (1 <= first) ” 
  &&  “ (first < 10) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ (first_digit_state_146 current first ) ” 
  &&  “ (special_filter_prefix_146 input_l i num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_7 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((last % ( 2 ) ) = 1)) (PreH2 : ((first % ( 2 ) ) = 1)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_146_pre_z input_l )) (PreH7 : (special_filter_safe_146 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < nums_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (current > 10)) (PreH14 : (INT_MIN <= current)) (PreH15 : (current <= INT_MAX)) (PreH16 : (1 <= first)) (PreH17 : (first < 10)) (PreH18 : (last = (current % ( 10 ) ))) (PreH19 : (first_digit_state_146 current first )) (PreH20 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= (num + 1 )) ” 
  &&  “ ((num + 1 ) <= (i + 1 )) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (first_digit_state_146 current first ) ” 
  &&  “ (first < 10) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ ((first % ( 2 ) ) = 1) ” 
  &&  “ ((last % ( 2 ) ) = 1) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) (num + 1 ) ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((last % ( 2 ) ) = 1)) (PreH2 : ((first % ( 2 ) ) = 1)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_146_pre_z input_l )) (PreH7 : (special_filter_safe_146 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < nums_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (current > 10)) (PreH14 : (INT_MIN <= current)) (PreH15 : (current <= INT_MAX)) (PreH16 : (1 <= first)) (PreH17 : (first < 10)) (PreH18 : (last = (current % ( 10 ) ))) (PreH19 : (first_digit_state_146 current first )) (PreH20 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (special_filter_prefix_146 input_l (i + 1 ) (num + 1 ) ) ”
  &&  emp
).

Definition specialFilter_entail_wit_7_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((last % ( 2 ) ) = 1)) (PreH2 : ((first % ( 2 ) ) = 1)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_146_pre_z input_l )) (PreH7 : (special_filter_safe_146 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < nums_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (current > 10)) (PreH14 : (INT_MIN <= current)) (PreH15 : (current <= INT_MAX)) (PreH16 : (1 <= first)) (PreH17 : (first < 10)) (PreH18 : (last = (current % ( 10 ) ))) (PreH19 : (first_digit_state_146 current first )) (PreH20 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (special_filter_prefix_146 input_l (i + 1 ) (num + 1 ) ) ”
.

Definition specialFilter_entail_wit_8_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((last % ( 2 ) ) <> 1)) (PreH2 : ((first % ( 2 ) ) = 1)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_146_pre_z input_l )) (PreH7 : (special_filter_safe_146 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < nums_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (current > 10)) (PreH14 : (INT_MIN <= current)) (PreH15 : (current <= INT_MAX)) (PreH16 : (1 <= first)) (PreH17 : (first < 10)) (PreH18 : (last = (current % ( 10 ) ))) (PreH19 : (first_digit_state_146 current first )) (PreH20 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  (“ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (first_digit_state_146 current first ) ” 
  &&  “ (first < 10) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ ((last % ( 2 ) ) <> 1) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l ))
  ||
  (“ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (first_digit_state_146 current first ) ” 
  &&  “ (first < 10) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ ((first % ( 2 ) ) <> 1) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l ))
.

Definition specialFilter_entail_wit_8_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : ((first % ( 2 ) ) <> 1)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (current > 10)) (PreH13 : (INT_MIN <= current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (1 <= first)) (PreH16 : (first < 10)) (PreH17 : (last = (current % ( 10 ) ))) (PreH18 : (first_digit_state_146 current first )) (PreH19 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  (“ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (first_digit_state_146 current first ) ” 
  &&  “ (first < 10) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ ((last % ( 2 ) ) <> 1) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l ))
  ||
  (“ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 10) ” 
  &&  “ (first_digit_state_146 current first ) ” 
  &&  “ (first < 10) ” 
  &&  “ (last = (current % ( 10 ) )) ” 
  &&  “ ((first % ( 2 ) ) <> 1) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l ))
.

Definition specialFilter_entail_wit_9 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current <= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current <= 10) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current <= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  emp
).

Definition specialFilter_entail_wit_9_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current <= 10)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN <= current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
.

Definition specialFilter_entail_wit_10_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (first_digit_state_146 current first )) (PreH13 : (first < 10)) (PreH14 : (last = (current % ( 10 ) ))) (PreH15 : ((first % ( 2 ) ) = 1)) (PreH16 : ((last % ( 2 ) ) = 1)) (PreH17 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_10_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (first_digit_state_146 current first )) (PreH13 : (first < 10)) (PreH14 : (last = (current % ( 10 ) ))) (PreH15 : ((last % ( 2 ) ) <> 1)) (PreH16 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_10_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (first: Z) (last: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 10)) (PreH12 : (first_digit_state_146 current first )) (PreH13 : (first < 10)) (PreH14 : (last = (current % ( 10 ) ))) (PreH15 : ((first % ( 2 ) ) <> 1)) (PreH16 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_entail_wit_10_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_146_pre_z input_l )) (PreH5 : (special_filter_safe_146 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < nums_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current <= 10)) (PreH12 : (special_filter_prefix_146 input_l (i + 1 ) num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (special_filter_prefix_146 input_l (i + 1 ) num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition specialFilter_return_wit_1 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (problem_146_spec_z input_l num ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (problem_146_spec_z input_l num ) ”
  &&  emp
).

Definition specialFilter_return_wit_1_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  TT && emp 
|--
  “ (problem_146_spec_z input_l num ) ”
.

Definition specialFilter_partial_solve_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_146_pre_z input_l )) (PreH6 : (special_filter_safe_146 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= nums_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (special_filter_prefix_146 input_l i num )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (i < nums_size_pre) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_146_pre_z input_l ) ” 
  &&  “ (special_filter_safe_146 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nums_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (special_filter_prefix_146 input_l i num ) ”
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_specialFilter_safety_wit_1 : specialFilter_safety_wit_1.
Axiom proof_of_specialFilter_safety_wit_2 : specialFilter_safety_wit_2.
Axiom proof_of_specialFilter_safety_wit_3 : specialFilter_safety_wit_3.
Axiom proof_of_specialFilter_safety_wit_4 : specialFilter_safety_wit_4.
Axiom proof_of_specialFilter_safety_wit_5 : specialFilter_safety_wit_5.
Axiom proof_of_specialFilter_safety_wit_6 : specialFilter_safety_wit_6.
Axiom proof_of_specialFilter_safety_wit_7 : specialFilter_safety_wit_7.
Axiom proof_of_specialFilter_safety_wit_8 : specialFilter_safety_wit_8.
Axiom proof_of_specialFilter_safety_wit_9 : specialFilter_safety_wit_9.
Axiom proof_of_specialFilter_safety_wit_10 : specialFilter_safety_wit_10.
Axiom proof_of_specialFilter_safety_wit_11 : specialFilter_safety_wit_11.
Axiom proof_of_specialFilter_safety_wit_12 : specialFilter_safety_wit_12.
Axiom proof_of_specialFilter_safety_wit_13 : specialFilter_safety_wit_13.
Axiom proof_of_specialFilter_safety_wit_14 : specialFilter_safety_wit_14.
Axiom proof_of_specialFilter_safety_wit_15 : specialFilter_safety_wit_15.
Axiom proof_of_specialFilter_safety_wit_16 : specialFilter_safety_wit_16.
Axiom proof_of_specialFilter_safety_wit_17 : specialFilter_safety_wit_17.
Axiom proof_of_specialFilter_safety_wit_18 : specialFilter_safety_wit_18.
Axiom proof_of_specialFilter_safety_wit_19 : specialFilter_safety_wit_19.
Axiom proof_of_specialFilter_safety_wit_20 : specialFilter_safety_wit_20.
Axiom proof_of_specialFilter_entail_wit_1 : specialFilter_entail_wit_1.
Axiom proof_of_specialFilter_entail_wit_2 : specialFilter_entail_wit_2.
Axiom proof_of_specialFilter_entail_wit_3 : specialFilter_entail_wit_3.
Axiom proof_of_specialFilter_entail_wit_4 : specialFilter_entail_wit_4.
Axiom proof_of_specialFilter_entail_wit_5 : specialFilter_entail_wit_5.
Axiom proof_of_specialFilter_entail_wit_6 : specialFilter_entail_wit_6.
Axiom proof_of_specialFilter_entail_wit_7 : specialFilter_entail_wit_7.
Axiom proof_of_specialFilter_entail_wit_8_1 : specialFilter_entail_wit_8_1.
Axiom proof_of_specialFilter_entail_wit_8_2 : specialFilter_entail_wit_8_2.
Axiom proof_of_specialFilter_entail_wit_9 : specialFilter_entail_wit_9.
Axiom proof_of_specialFilter_entail_wit_10_1 : specialFilter_entail_wit_10_1.
Axiom proof_of_specialFilter_entail_wit_10_2 : specialFilter_entail_wit_10_2.
Axiom proof_of_specialFilter_entail_wit_10_3 : specialFilter_entail_wit_10_3.
Axiom proof_of_specialFilter_entail_wit_10_4 : specialFilter_entail_wit_10_4.
Axiom proof_of_specialFilter_return_wit_1 : specialFilter_return_wit_1.
Axiom proof_of_specialFilter_partial_solve_wit_1 : specialFilter_partial_solve_wit_1.

End VC_Correct.
