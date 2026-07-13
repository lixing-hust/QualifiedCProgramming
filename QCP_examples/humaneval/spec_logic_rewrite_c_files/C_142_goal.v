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
Require Import coins_142.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function sum_squares -----*)

Definition sum_squares_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_142_pre_z input_l )) (PreH5 : (sum_squares_int_range_142 input_l )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sum_squares_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_142_pre_z input_l )) (PreH5 : (sum_squares_int_range_142 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sum_squares_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_142_pre_z input_l )) (PreH6 : (sum_squares_int_range_142 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i <> (INT_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition sum_squares_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_142_pre_z input_l )) (PreH6 : (sum_squares_int_range_142 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sum_squares_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_142_pre_z input_l )) (PreH6 : (sum_squares_int_range_142 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sum_squares_safety_wit_6 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) )) ”
).

Definition sum_squares_safety_wit_6_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_6_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) )) ”
.

Definition sum_squares_safety_wit_7 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
).

Definition sum_squares_safety_wit_7_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_7_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
.

Definition sum_squares_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) <> 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i <> (INT_MIN)) \/ (4 <> (-1))) ” 
  &&  “ (4 <> 0) ”
.

Definition sum_squares_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) <> 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition sum_squares_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) <> 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sum_squares_safety_wit_11 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) )) ”
).

Definition sum_squares_safety_wit_11_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_11_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) )) ”
.

Definition sum_squares_safety_wit_12 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) )) ”
).

Definition sum_squares_safety_wit_12_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_12_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) )) ”
.

Definition sum_squares_safety_wit_13 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
).

Definition sum_squares_safety_wit_13_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_13_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
.

Definition sum_squares_safety_wit_14 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i input_l 0) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i input_l 0) )) ”
).

Definition sum_squares_safety_wit_14_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth i input_l 0) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_14_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + (Znth i input_l 0) )) ”
.

Definition sum_squares_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sum: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_142_pre_z input_l )) (PreH5 : (sum_squares_int_range_142 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (sum = (sum_prefix_142 ((i + 1 )) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sum_squares_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_142_pre_z input_l )) (PreH5 : (sum_squares_int_range_142 input_l )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (0 = (sum_prefix_142 (0) (input_l))) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_142_pre_z input_l )) (PreH5 : (sum_squares_int_range_142 input_l )) ,
  TT && emp 
|--
  “ (0 = (sum_prefix_142 (0) (input_l))) ”
  &&  emp
).

Definition sum_squares_entail_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_142_pre_z input_l )) (PreH5 : (sum_squares_int_range_142 input_l )) ,
  TT && emp 
|--
  “ (0 = (sum_prefix_142 (0) (input_l))) ”
.

Definition sum_squares_entail_wit_2_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ ((sum + (Znth i input_l 0) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= (sum + (Znth i input_l 0) )) ” 
  &&  “ ((sum + (Znth i input_l 0) ) <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + (Znth i input_l 0) )) ” 
  &&  “ ((sum + (Znth i input_l 0) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition sum_squares_entail_wit_2_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (Znth i input_l 0) ) <= INT_MAX) ”
.

Definition sum_squares_entail_wit_2_1_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN <= (sum + (Znth i input_l 0) )) ”
.

Definition sum_squares_entail_wit_2_1_split_goal_3 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (Znth i input_l 0) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ”
.

Definition sum_squares_entail_wit_2_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) )) ” 
  &&  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) )) ” 
  &&  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition sum_squares_entail_wit_2_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) <= INT_MAX) ”
.

Definition sum_squares_entail_wit_2_2_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN <= (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) )) ”
.

Definition sum_squares_entail_wit_2_2_split_goal_3 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ”
.

Definition sum_squares_entail_wit_2_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) )) ” 
  &&  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) )) ” 
  &&  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition sum_squares_entail_wit_2_3_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) <= INT_MAX) ”
.

Definition sum_squares_entail_wit_2_3_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN <= (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) )) ”
.

Definition sum_squares_entail_wit_2_3_split_goal_3 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) = (sum_prefix_142 ((i + 1 )) (input_l))) ”
.

Definition sum_squares_entail_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sum: Z) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_142_pre_z input_l )) (PreH5 : (sum_squares_int_range_142 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (sum = (sum_prefix_142 ((i + 1 )) (input_l)))) (PreH9 : (INT_MIN <= sum)) (PreH10 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (sum = (sum_prefix_142 ((i + 1 )) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition sum_squares_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_142_pre_z input_l )) (PreH6 : (sum_squares_int_range_142 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (problem_142_spec_z input_l sum ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_142_pre_z input_l )) (PreH6 : (sum_squares_int_range_142 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_142_spec_z input_l sum ) ”
  &&  emp
).

Definition sum_squares_return_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_142_pre_z input_l )) (PreH6 : (sum_squares_int_range_142 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_142_spec_z input_l sum ) ”
.

Definition sum_squares_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum = (sum_prefix_142 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition sum_squares_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 3 ) ) = 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_142_pre_z input_l )) (PreH7 : (sum_squares_int_range_142 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i <= lst_size_pre)) (PreH10 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH11 : (INT_MIN <= sum)) (PreH12 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum = (sum_prefix_142 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition sum_squares_partial_solve_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum = (sum_prefix_142 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition sum_squares_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum = (sum_prefix_142 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition sum_squares_partial_solve_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) = 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum = (sum_prefix_142 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition sum_squares_partial_solve_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((i % ( 4 ) ) <> 0)) (PreH2 : ((i % ( 3 ) ) <> 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_142_pre_z input_l )) (PreH8 : (sum_squares_int_range_142 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= lst_size_pre)) (PreH11 : (sum = (sum_prefix_142 (i) (input_l)))) (PreH12 : (INT_MIN <= sum)) (PreH13 : (sum <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) <> 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre_z input_l ) ” 
  &&  “ (sum_squares_int_range_142 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum = (sum_prefix_142 (i) (input_l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_sum_squares_safety_wit_1 : sum_squares_safety_wit_1.
Axiom proof_of_sum_squares_safety_wit_2 : sum_squares_safety_wit_2.
Axiom proof_of_sum_squares_safety_wit_3 : sum_squares_safety_wit_3.
Axiom proof_of_sum_squares_safety_wit_4 : sum_squares_safety_wit_4.
Axiom proof_of_sum_squares_safety_wit_5 : sum_squares_safety_wit_5.
Axiom proof_of_sum_squares_safety_wit_6 : sum_squares_safety_wit_6.
Axiom proof_of_sum_squares_safety_wit_7 : sum_squares_safety_wit_7.
Axiom proof_of_sum_squares_safety_wit_8 : sum_squares_safety_wit_8.
Axiom proof_of_sum_squares_safety_wit_9 : sum_squares_safety_wit_9.
Axiom proof_of_sum_squares_safety_wit_10 : sum_squares_safety_wit_10.
Axiom proof_of_sum_squares_safety_wit_11 : sum_squares_safety_wit_11.
Axiom proof_of_sum_squares_safety_wit_12 : sum_squares_safety_wit_12.
Axiom proof_of_sum_squares_safety_wit_13 : sum_squares_safety_wit_13.
Axiom proof_of_sum_squares_safety_wit_14 : sum_squares_safety_wit_14.
Axiom proof_of_sum_squares_safety_wit_15 : sum_squares_safety_wit_15.
Axiom proof_of_sum_squares_entail_wit_1 : sum_squares_entail_wit_1.
Axiom proof_of_sum_squares_entail_wit_2_1 : sum_squares_entail_wit_2_1.
Axiom proof_of_sum_squares_entail_wit_2_2 : sum_squares_entail_wit_2_2.
Axiom proof_of_sum_squares_entail_wit_2_3 : sum_squares_entail_wit_2_3.
Axiom proof_of_sum_squares_entail_wit_3 : sum_squares_entail_wit_3.
Axiom proof_of_sum_squares_return_wit_1 : sum_squares_return_wit_1.
Axiom proof_of_sum_squares_partial_solve_wit_1 : sum_squares_partial_solve_wit_1.
Axiom proof_of_sum_squares_partial_solve_wit_2 : sum_squares_partial_solve_wit_2.
Axiom proof_of_sum_squares_partial_solve_wit_3 : sum_squares_partial_solve_wit_3.
Axiom proof_of_sum_squares_partial_solve_wit_4 : sum_squares_partial_solve_wit_4.
Axiom proof_of_sum_squares_partial_solve_wit_5 : sum_squares_partial_solve_wit_5.
Axiom proof_of_sum_squares_partial_solve_wit_6 : sum_squares_partial_solve_wit_6.

End VC_Correct.
