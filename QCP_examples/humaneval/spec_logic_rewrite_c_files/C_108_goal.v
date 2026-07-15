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
Require Import coins_108.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function abs -----*)

Definition abs_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition abs_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition abs_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
).

Definition abs_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
.

Definition abs_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
).

Definition abs_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
.

(*----- Function count_nums -----*)

Definition count_nums_safety_wit_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) ,
  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_nums_safety_wit_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_nums_safety_wit_3 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN < current)) (PreH12 : (current <= INT_MAX)) (PreH13 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_nums_safety_wit_4 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((num + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num + 1 )) ”
.

Definition count_nums_safety_wit_5 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_nums_safety_wit_6 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current <= 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "digit_sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_nums_safety_wit_7 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN < current)) (PreH12 : (current <= 0)) (PreH13 : (0 <= w)) (PreH14 : (w <= INT_MAX)) (PreH15 : (INT_MIN < digit_sum)) (PreH16 : (digit_sum < INT_MAX)) (PreH17 : (signed_digit_sum_state_108 current w digit_sum )) (PreH18 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition count_nums_safety_wit_8 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((digit_sum + (w % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit_sum + (w % ( 10 ) ) )) ”
) \/
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((digit_sum + (w % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit_sum + (w % ( 10 ) ) )) ”
).

Definition count_nums_safety_wit_8_split_goal_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((digit_sum + (w % ( 10 ) ) ) <= INT_MAX) ”
.

Definition count_nums_safety_wit_8_split_goal_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((INT_MIN) <= (digit_sum + (w % ( 10 ) ) )) ”
.

Definition count_nums_safety_wit_9 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((w <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition count_nums_safety_wit_10 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition count_nums_safety_wit_11 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> (digit_sum + (w % ( 10 ) ) ))
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((w <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition count_nums_safety_wit_12 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> (digit_sum + (w % ( 10 ) ) ))
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition count_nums_safety_wit_13 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((digit_sum - w ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit_sum - w )) ”
) \/
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((digit_sum - w ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit_sum - w )) ”
).

Definition count_nums_safety_wit_13_split_goal_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((digit_sum - w ) <= INT_MAX) ”
.

Definition count_nums_safety_wit_13_split_goal_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((INT_MIN) <= (digit_sum - w )) ”
.

Definition count_nums_safety_wit_14 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (w_addr_v: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN < current)) (PreH12 : (current <= 0)) (PreH13 : (INT_MIN < digit_sum)) (PreH14 : (digit_sum < INT_MAX)) (PreH15 : (signed_digit_sum_positive_108 current digit_sum )) (PreH16 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "w" ) )) # Int  |-> w_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_nums_safety_wit_15 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (w_addr_v: Z) (PreH1 : (digit_sum > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "w" ) )) # Int  |-> w_addr_v)
|--
  “ ((num + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num + 1 )) ”
.

Definition count_nums_safety_wit_16 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (w_addr_v: Z) (PreH1 : (digit_sum > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "digit_sum" ) )) # Int  |-> digit_sum)
  **  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "w" ) )) # Int  |-> w_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_nums_safety_wit_17 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 0)) (PreH12 : (count_nums_prefix_108 input_l (i + 1 ) num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_nums_safety_wit_18 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current <= 0)) (PreH12 : (digit_sum > 0)) (PreH13 : (signed_digit_sum_positive_108 current digit_sum )) (PreH14 : (count_nums_prefix_108 input_l (i + 1 ) num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_nums_safety_wit_19 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current <= 0)) (PreH12 : (digit_sum <= 0)) (PreH13 : (signed_digit_sum_positive_108 current digit_sum )) (PreH14 : (count_nums_prefix_108 input_l (i + 1 ) num )) ,
  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_nums_entail_wit_1 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (count_nums_prefix_108 input_l 0 0 ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l 0 0 ) ”
  &&  emp
).

Definition count_nums_entail_wit_1_split_goal_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l 0 0 ) ”
.

Definition count_nums_entail_wit_2 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN < (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (count_nums_prefix_108 input_l i num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (INT_MIN < (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
  &&  emp
).

Definition count_nums_entail_wit_2_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) <= INT_MAX) ”
.

Definition count_nums_entail_wit_2_split_goal_2 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (INT_MIN < (Znth i input_l 0)) ”
.

Definition count_nums_entail_wit_2_split_goal_3 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
.

Definition count_nums_entail_wit_3 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= (num + 1 )) ” 
  &&  “ ((num + 1 ) <= (i + 1 )) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current > 0) ” 
  &&  “ (count_nums_prefix_108 input_l (i + 1 ) (num + 1 ) ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l (i + 1 ) (num + 1 ) ) ”
  &&  emp
).

Definition count_nums_entail_wit_3_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l (i + 1 ) (num + 1 ) ) ”
.

Definition count_nums_entail_wit_4 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (retval: Z) (PreH1 : (retval = (Zabs (current)))) (PreH2 : (current <= 0)) (PreH3 : (0 <= n_size_pre)) (PreH4 : (n_size_pre < INT_MAX)) (PreH5 : (n_size_pre = (Zlength (input_l)))) (PreH6 : (problem_108_pre_z input_l )) (PreH7 : (count_nums_safe_108 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < n_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (INT_MIN < current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN < current) ” 
  &&  “ (current <= 0) ” 
  &&  “ (retval = (Zabs (current))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (signed_digit_sum_state_108 current retval 0 ) ” 
  &&  “ (count_nums_prefix_108 input_l i num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (retval: Z) (PreH1 : (retval = (Zabs (current)))) (PreH2 : (current <= 0)) (PreH3 : (0 <= n_size_pre)) (PreH4 : (n_size_pre < INT_MAX)) (PreH5 : (n_size_pre = (Zlength (input_l)))) (PreH6 : (problem_108_pre_z input_l )) (PreH7 : (count_nums_safe_108 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < n_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (INT_MIN < current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (signed_digit_sum_state_108 current retval 0 ) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition count_nums_entail_wit_4_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (retval: Z) (PreH1 : (retval = (Zabs (current)))) (PreH2 : (current <= 0)) (PreH3 : (0 <= n_size_pre)) (PreH4 : (n_size_pre < INT_MAX)) (PreH5 : (n_size_pre = (Zlength (input_l)))) (PreH6 : (problem_108_pre_z input_l )) (PreH7 : (count_nums_safe_108 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < n_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (INT_MIN < current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (signed_digit_sum_state_108 current retval 0 ) ”
.

Definition count_nums_entail_wit_4_split_goal_2 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (retval: Z) (PreH1 : (retval = (Zabs (current)))) (PreH2 : (current <= 0)) (PreH3 : (0 <= n_size_pre)) (PreH4 : (n_size_pre < INT_MAX)) (PreH5 : (n_size_pre = (Zlength (input_l)))) (PreH6 : (problem_108_pre_z input_l )) (PreH7 : (count_nums_safe_108 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < n_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (INT_MIN < current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (retval <= INT_MAX) ”
.

Definition count_nums_entail_wit_4_split_goal_3 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (retval: Z) (PreH1 : (retval = (Zabs (current)))) (PreH2 : (current <= 0)) (PreH3 : (0 <= n_size_pre)) (PreH4 : (n_size_pre < INT_MAX)) (PreH5 : (n_size_pre = (Zlength (input_l)))) (PreH6 : (problem_108_pre_z input_l )) (PreH7 : (count_nums_safe_108 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < n_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (INT_MIN < current)) (PreH14 : (current <= INT_MAX)) (PreH15 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition count_nums_entail_wit_5 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (w: Z) (digit_sum: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (INT_MIN < current)) (PreH12 : (current <= 0)) (PreH13 : (w = (Zabs (current)))) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (digit_sum = 0)) (PreH17 : (signed_digit_sum_state_108 current w digit_sum )) (PreH18 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN < current) ” 
  &&  “ (current <= 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= INT_MAX) ” 
  &&  “ (INT_MIN < digit_sum) ” 
  &&  “ (digit_sum < INT_MAX) ” 
  &&  “ (signed_digit_sum_state_108 current w digit_sum ) ” 
  &&  “ (count_nums_prefix_108 input_l i num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_6 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN < current) ” 
  &&  “ (current <= 0) ” 
  &&  “ (0 <= (w ÷ 10 )) ” 
  &&  “ ((w ÷ 10 ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (digit_sum + (w % ( 10 ) ) )) ” 
  &&  “ ((digit_sum + (w % ( 10 ) ) ) < INT_MAX) ” 
  &&  “ (signed_digit_sum_state_108 current (w ÷ 10 ) (digit_sum + (w % ( 10 ) ) ) ) ” 
  &&  “ (count_nums_prefix_108 input_l i num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (signed_digit_sum_state_108 current (w ÷ 10 ) (digit_sum + (w % ( 10 ) ) ) ) ” 
  &&  “ ((digit_sum + (w % ( 10 ) ) ) < INT_MAX) ” 
  &&  “ (INT_MIN < (digit_sum + (w % ( 10 ) ) )) ” 
  &&  “ ((w ÷ 10 ) <= INT_MAX) ” 
  &&  “ (0 <= (w ÷ 10 )) ”
  &&  emp
).

Definition count_nums_entail_wit_6_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (signed_digit_sum_state_108 current (w ÷ 10 ) (digit_sum + (w % ( 10 ) ) ) ) ”
.

Definition count_nums_entail_wit_6_split_goal_2 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ ((digit_sum + (w % ( 10 ) ) ) < INT_MAX) ”
.

Definition count_nums_entail_wit_6_split_goal_3 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (INT_MIN < (digit_sum + (w % ( 10 ) ) )) ”
.

Definition count_nums_entail_wit_6_split_goal_4 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ ((w ÷ 10 ) <= INT_MAX) ”
.

Definition count_nums_entail_wit_6_split_goal_5 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w >= 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (0 <= (w ÷ 10 )) ”
.

Definition count_nums_entail_wit_7 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN < current) ” 
  &&  “ (current <= 0) ” 
  &&  “ (INT_MIN < (digit_sum - w )) ” 
  &&  “ ((digit_sum - w ) < INT_MAX) ” 
  &&  “ (signed_digit_sum_positive_108 current (digit_sum - w ) ) ” 
  &&  “ (count_nums_prefix_108 input_l i num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (signed_digit_sum_positive_108 current (digit_sum - w ) ) ” 
  &&  “ (INT_MIN < (digit_sum - w )) ”
  &&  emp
).

Definition count_nums_entail_wit_7_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (signed_digit_sum_positive_108 current (digit_sum - w ) ) ”
.

Definition count_nums_entail_wit_7_split_goal_2 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (digit_sum: Z) (w: Z) (current: Z) (num: Z) (i: Z) (PreH1 : (w < 10)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (0 <= w)) (PreH15 : (w <= INT_MAX)) (PreH16 : (INT_MIN < digit_sum)) (PreH17 : (digit_sum < INT_MAX)) (PreH18 : (signed_digit_sum_state_108 current w digit_sum )) (PreH19 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (INT_MIN < (digit_sum - w )) ”
.

Definition count_nums_entail_wit_8 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (digit_sum > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= (num + 1 )) ” 
  &&  “ ((num + 1 ) <= (i + 1 )) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current <= 0) ” 
  &&  “ (digit_sum > 0) ” 
  &&  “ (signed_digit_sum_positive_108 current digit_sum ) ” 
  &&  “ (count_nums_prefix_108 input_l (i + 1 ) (num + 1 ) ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (digit_sum > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l (i + 1 ) (num + 1 ) ) ”
  &&  emp
).

Definition count_nums_entail_wit_8_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (digit_sum > 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l (i + 1 ) (num + 1 ) ) ”
.

Definition count_nums_entail_wit_9 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (digit_sum <= 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (current <= 0) ” 
  &&  “ (digit_sum <= 0) ” 
  &&  “ (signed_digit_sum_positive_108 current digit_sum ) ” 
  &&  “ (count_nums_prefix_108 input_l (i + 1 ) num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (digit_sum <= 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l (i + 1 ) num ) ”
  &&  emp
).

Definition count_nums_entail_wit_9_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (digit_sum <= 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= 0)) (PreH14 : (INT_MIN < digit_sum)) (PreH15 : (digit_sum < INT_MAX)) (PreH16 : (signed_digit_sum_positive_108 current digit_sum )) (PreH17 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (count_nums_prefix_108 input_l (i + 1 ) num ) ”
.

Definition count_nums_entail_wit_10_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current > 0)) (PreH12 : (count_nums_prefix_108 input_l (i + 1 ) num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (count_nums_prefix_108 input_l (i + 1 ) num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_10_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current <= 0)) (PreH12 : (digit_sum > 0)) (PreH13 : (signed_digit_sum_positive_108 current digit_sum )) (PreH14 : (count_nums_prefix_108 input_l (i + 1 ) num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (count_nums_prefix_108 input_l (i + 1 ) num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_10_3 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (digit_sum: Z) (PreH1 : (0 <= n_size_pre)) (PreH2 : (n_size_pre < INT_MAX)) (PreH3 : (n_size_pre = (Zlength (input_l)))) (PreH4 : (problem_108_pre_z input_l )) (PreH5 : (count_nums_safe_108 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < n_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (current <= 0)) (PreH12 : (digit_sum <= 0)) (PreH13 : (signed_digit_sum_positive_108 current digit_sum )) (PreH14 : (count_nums_prefix_108 input_l (i + 1 ) num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (count_nums_prefix_108 input_l (i + 1 ) num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_return_wit_1 := 
(
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (problem_108_spec_z input_l num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
) \/
(
forall (n_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (problem_108_spec_z input_l num ) ”
  &&  emp
).

Definition count_nums_return_wit_1_split_goal_1 := 
forall (n_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  TT && emp 
|--
  “ (problem_108_spec_z input_l num ) ”
.

Definition count_nums_partial_solve_wit_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < n_size_pre)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (i < n_size_pre) ” 
  &&  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (count_nums_prefix_108 input_l i num ) ”
  &&  (((n_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i n_pre i 0 n_size_pre input_l )
.

Definition count_nums_partial_solve_wit_2_pure := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current <= 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "digit_sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (INT_MIN < current) ” 
  &&  “ (current <= INT_MAX) ”
.

Definition count_nums_partial_solve_wit_2_aux := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (current: Z) (PreH1 : (current <= 0)) (PreH2 : (0 <= n_size_pre)) (PreH3 : (n_size_pre < INT_MAX)) (PreH4 : (n_size_pre = (Zlength (input_l)))) (PreH5 : (problem_108_pre_z input_l )) (PreH6 : (count_nums_safe_108 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < n_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (INT_MIN < current)) (PreH13 : (current <= INT_MAX)) (PreH14 : (count_nums_prefix_108 input_l i num )) ,
  (IntArray.full n_pre n_size_pre input_l )
|--
  “ (INT_MIN < current) ” 
  &&  “ (current <= INT_MAX) ” 
  &&  “ (current <= 0) ” 
  &&  “ (0 <= n_size_pre) ” 
  &&  “ (n_size_pre < INT_MAX) ” 
  &&  “ (n_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_108_pre_z input_l ) ” 
  &&  “ (count_nums_safe_108 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (INT_MIN < current) ” 
  &&  “ (current <= INT_MAX) ” 
  &&  “ (count_nums_prefix_108 input_l i num ) ”
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_partial_solve_wit_2 := count_nums_partial_solve_wit_2_pure -> count_nums_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_count_nums_safety_wit_1 : count_nums_safety_wit_1.
Axiom proof_of_count_nums_safety_wit_2 : count_nums_safety_wit_2.
Axiom proof_of_count_nums_safety_wit_3 : count_nums_safety_wit_3.
Axiom proof_of_count_nums_safety_wit_4 : count_nums_safety_wit_4.
Axiom proof_of_count_nums_safety_wit_5 : count_nums_safety_wit_5.
Axiom proof_of_count_nums_safety_wit_6 : count_nums_safety_wit_6.
Axiom proof_of_count_nums_safety_wit_7 : count_nums_safety_wit_7.
Axiom proof_of_count_nums_safety_wit_8 : count_nums_safety_wit_8.
Axiom proof_of_count_nums_safety_wit_9 : count_nums_safety_wit_9.
Axiom proof_of_count_nums_safety_wit_10 : count_nums_safety_wit_10.
Axiom proof_of_count_nums_safety_wit_11 : count_nums_safety_wit_11.
Axiom proof_of_count_nums_safety_wit_12 : count_nums_safety_wit_12.
Axiom proof_of_count_nums_safety_wit_13 : count_nums_safety_wit_13.
Axiom proof_of_count_nums_safety_wit_14 : count_nums_safety_wit_14.
Axiom proof_of_count_nums_safety_wit_15 : count_nums_safety_wit_15.
Axiom proof_of_count_nums_safety_wit_16 : count_nums_safety_wit_16.
Axiom proof_of_count_nums_safety_wit_17 : count_nums_safety_wit_17.
Axiom proof_of_count_nums_safety_wit_18 : count_nums_safety_wit_18.
Axiom proof_of_count_nums_safety_wit_19 : count_nums_safety_wit_19.
Axiom proof_of_count_nums_entail_wit_1 : count_nums_entail_wit_1.
Axiom proof_of_count_nums_entail_wit_2 : count_nums_entail_wit_2.
Axiom proof_of_count_nums_entail_wit_3 : count_nums_entail_wit_3.
Axiom proof_of_count_nums_entail_wit_4 : count_nums_entail_wit_4.
Axiom proof_of_count_nums_entail_wit_5 : count_nums_entail_wit_5.
Axiom proof_of_count_nums_entail_wit_6 : count_nums_entail_wit_6.
Axiom proof_of_count_nums_entail_wit_7 : count_nums_entail_wit_7.
Axiom proof_of_count_nums_entail_wit_8 : count_nums_entail_wit_8.
Axiom proof_of_count_nums_entail_wit_9 : count_nums_entail_wit_9.
Axiom proof_of_count_nums_entail_wit_10_1 : count_nums_entail_wit_10_1.
Axiom proof_of_count_nums_entail_wit_10_2 : count_nums_entail_wit_10_2.
Axiom proof_of_count_nums_entail_wit_10_3 : count_nums_entail_wit_10_3.
Axiom proof_of_count_nums_return_wit_1 : count_nums_return_wit_1.
Axiom proof_of_count_nums_partial_solve_wit_1 : count_nums_partial_solve_wit_1.
Axiom proof_of_count_nums_partial_solve_wit_2_pure : count_nums_partial_solve_wit_2_pure.
Axiom proof_of_count_nums_partial_solve_wit_2 : count_nums_partial_solve_wit_2.

End VC_Correct.
