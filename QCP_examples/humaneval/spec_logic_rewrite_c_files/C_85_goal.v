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
Require Import coins_85.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function add -----*)

Definition add_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_safety_wit_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
).

Definition add_safety_wit_3_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ”
.

Definition add_safety_wit_3_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
.

Definition add_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 2 )) ”
.

Definition add_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth ((i * 2 ) + 1 ) input_l 0) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition add_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
.

Definition add_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 2 )) ”
.

Definition add_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_safety_wit_14 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth ((i * 2 ) + 1 ) input_l 0) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth ((i * 2 ) + 1 ) input_l 0) )) ”
).

Definition add_safety_wit_14_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) <= INT_MAX) ”
.

Definition add_safety_wit_14_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + (Znth ((i * 2 ) + 1 ) input_l 0) )) ”
.

Definition add_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
.

Definition add_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((i * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 2 )) ”
.

Definition add_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_safety_wit_18 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_safety_wit_19 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sum: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : (((2 * i ) + 1 ) < lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 ((i + 1 )) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition add_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= (INT_MAX ÷ 2 )) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_85_pre_z input_l ) ” 
  &&  “ (add_sum_int_range_85 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((2 * 0 ) <= lst_size_pre) ” 
  &&  “ (0 = (add_prefix_sum_85 (0) (input_l))) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) ,
  TT && emp 
|--
  “ (0 = (add_prefix_sum_85 (0) (input_l))) ”
  &&  emp
).

Definition add_entail_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) ,
  TT && emp 
|--
  “ (0 = (add_prefix_sum_85 (0) (input_l))) ”
.

Definition add_entail_wit_2_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) <> 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= (INT_MAX ÷ 2 )) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_85_pre_z input_l ) ” 
  &&  “ (add_sum_int_range_85 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (((2 * i ) + 1 ) < lst_size_pre) ” 
  &&  “ (sum = (add_prefix_sum_85 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) <> 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (sum = (add_prefix_sum_85 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition add_entail_wit_2_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) <> 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (sum = (add_prefix_sum_85 ((i + 1 )) (input_l))) ”
.

Definition add_entail_wit_2_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= (INT_MAX ÷ 2 )) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_85_pre_z input_l ) ” 
  &&  “ (add_sum_int_range_85 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (((2 * i ) + 1 ) < lst_size_pre) ” 
  &&  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) = (add_prefix_sum_85 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= (sum + (Znth ((i * 2 ) + 1 ) input_l 0) )) ” 
  &&  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + (Znth ((i * 2 ) + 1 ) input_l 0) )) ” 
  &&  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) = (add_prefix_sum_85 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition add_entail_wit_2_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) <= INT_MAX) ”
.

Definition add_entail_wit_2_2_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN <= (sum + (Znth ((i * 2 ) + 1 ) input_l 0) )) ”
.

Definition add_entail_wit_2_2_split_goal_3 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (Znth ((i * 2 ) + 1 ) input_l 0) ) = (add_prefix_sum_85 ((i + 1 )) (input_l))) ”
.

Definition add_entail_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sum: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_85_pre_z input_l )) (PreH5 : (add_sum_int_range_85 input_l )) (PreH6 : (0 <= i)) (PreH7 : (((2 * i ) + 1 ) < lst_size_pre)) (PreH8 : (sum = (add_prefix_sum_85 ((i + 1 )) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= (INT_MAX ÷ 2 )) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_85_pre_z input_l ) ” 
  &&  “ (add_sum_int_range_85 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((2 * (i + 1 ) ) <= lst_size_pre) ” 
  &&  “ (sum = (add_prefix_sum_85 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition add_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (problem_85_spec_z input_l sum ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_85_spec_z input_l sum ) ”
  &&  emp
).

Definition add_return_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_85_spec_z input_l sum ) ”
.

Definition add_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_85_pre_z input_l )) (PreH6 : (add_sum_int_range_85 input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= lst_size_pre)) (PreH9 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= (INT_MAX ÷ 2 )) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_85_pre_z input_l ) ” 
  &&  “ (add_sum_int_range_85 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (sum = (add_prefix_sum_85 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (((i * 2 ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i * 2 ) + 1 ) input_l 0))
  **  (IntArray.missing_i lst_pre ((i * 2 ) + 1 ) 0 lst_size_pre input_l )
.

Definition add_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0)) (PreH2 : (((i * 2 ) + 1 ) < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre <= (INT_MAX ÷ 2 ))) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_85_pre_z input_l )) (PreH7 : (add_sum_int_range_85 input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= lst_size_pre)) (PreH10 : (sum = (add_prefix_sum_85 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (((Znth ((i * 2 ) + 1 ) input_l 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= (INT_MAX ÷ 2 )) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_85_pre_z input_l ) ” 
  &&  “ (add_sum_int_range_85 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (sum = (add_prefix_sum_85 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (((i * 2 ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i * 2 ) + 1 ) input_l 0))
  **  (IntArray.missing_i lst_pre ((i * 2 ) + 1 ) 0 lst_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_add_safety_wit_1 : add_safety_wit_1.
Axiom proof_of_add_safety_wit_2 : add_safety_wit_2.
Axiom proof_of_add_safety_wit_3 : add_safety_wit_3.
Axiom proof_of_add_safety_wit_4 : add_safety_wit_4.
Axiom proof_of_add_safety_wit_5 : add_safety_wit_5.
Axiom proof_of_add_safety_wit_6 : add_safety_wit_6.
Axiom proof_of_add_safety_wit_7 : add_safety_wit_7.
Axiom proof_of_add_safety_wit_8 : add_safety_wit_8.
Axiom proof_of_add_safety_wit_9 : add_safety_wit_9.
Axiom proof_of_add_safety_wit_10 : add_safety_wit_10.
Axiom proof_of_add_safety_wit_11 : add_safety_wit_11.
Axiom proof_of_add_safety_wit_12 : add_safety_wit_12.
Axiom proof_of_add_safety_wit_13 : add_safety_wit_13.
Axiom proof_of_add_safety_wit_14 : add_safety_wit_14.
Axiom proof_of_add_safety_wit_15 : add_safety_wit_15.
Axiom proof_of_add_safety_wit_16 : add_safety_wit_16.
Axiom proof_of_add_safety_wit_17 : add_safety_wit_17.
Axiom proof_of_add_safety_wit_18 : add_safety_wit_18.
Axiom proof_of_add_safety_wit_19 : add_safety_wit_19.
Axiom proof_of_add_entail_wit_1 : add_entail_wit_1.
Axiom proof_of_add_entail_wit_2_1 : add_entail_wit_2_1.
Axiom proof_of_add_entail_wit_2_2 : add_entail_wit_2_2.
Axiom proof_of_add_entail_wit_3 : add_entail_wit_3.
Axiom proof_of_add_return_wit_1 : add_return_wit_1.
Axiom proof_of_add_partial_solve_wit_1 : add_partial_solve_wit_1.
Axiom proof_of_add_partial_solve_wit_2 : add_partial_solve_wit_2.

End VC_Correct.
