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
Require Import coins_109.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function move_one_ball -----*)

Definition move_one_ball_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) ,
  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition move_one_ball_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) ,
  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition move_one_ball_safety_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_size_pre = 0)) (PreH2 : (arr_pre <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) ,
  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition move_one_ball_safety_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_size_pre <> 0)) (PreH2 : (arr_pre <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition move_one_ball_safety_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition move_one_ball_safety_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition move_one_ball_safety_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) < (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ ((num + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num + 1 )) ”
.

Definition move_one_ball_safety_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) < (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition move_one_ball_safety_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_109_pre_z input_l )) (PreH5 : (move_one_ball_safe_109 input_l )) (PreH6 : (1 <= i)) (PreH7 : (i < arr_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (move_one_ball_prefix_109 input_l (i + 1 ) num )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition move_one_ball_safety_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_109_pre_z input_l )) (PreH5 : (move_one_ball_safe_109 input_l )) (PreH6 : (1 <= i)) (PreH7 : (i < arr_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (move_one_ball_prefix_109 input_l (i + 1 ) num )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition move_one_ball_safety_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((arr_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (arr_size_pre - 1 )) ”
.

Definition move_one_ball_safety_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition move_one_ball_safety_wit_13 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition move_one_ball_safety_wit_14 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) > (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ ((num + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num + 1 )) ”
.

Definition move_one_ball_safety_wit_15 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) > (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition move_one_ball_safety_wit_16 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i_addr_v: Z) (PreH1 : (0 < arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_109_pre_z input_l )) (PreH5 : (move_one_ball_safe_109 input_l )) (PreH6 : (0 <= num)) (PreH7 : (num <= arr_size_pre)) (PreH8 : (move_one_ball_wrap_109 input_l num )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition move_one_ball_safety_wit_17 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i_addr_v: Z) (PreH1 : (num < 2)) (PreH2 : (0 < arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (0 <= num)) (PreH8 : (num <= arr_size_pre)) (PreH9 : (move_one_ball_wrap_109 input_l num )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition move_one_ball_safety_wit_18 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i_addr_v: Z) (PreH1 : (num >= 2)) (PreH2 : (0 < arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (0 <= num)) (PreH8 : (num <= arr_size_pre)) (PreH9 : (move_one_ball_wrap_109 input_l num )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition move_one_ball_entail_wit_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_size_pre <> 0)) (PreH2 : (arr_pre <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= arr_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (move_one_ball_prefix_109 input_l 1 0 ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_size_pre <> 0)) (PreH2 : (arr_pre <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) ,
  TT && emp 
|--
  “ (move_one_ball_prefix_109 input_l 1 0 ) ”
  &&  emp
).

Definition move_one_ball_entail_wit_1_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_size_pre <> 0)) (PreH2 : (arr_pre <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) ,
  TT && emp 
|--
  “ (move_one_ball_prefix_109 input_l 1 0 ) ”
.

Definition move_one_ball_entail_wit_2 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) < (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (0 <= (num + 1 )) ” 
  &&  “ ((num + 1 ) <= (i + 1 )) ” 
  &&  “ (move_one_ball_prefix_109 input_l (i + 1 ) (num + 1 ) ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) < (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_prefix_109 input_l (i + 1 ) (num + 1 ) ) ”
  &&  emp
).

Definition move_one_ball_entail_wit_2_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) < (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_prefix_109 input_l (i + 1 ) (num + 1 ) ) ”
.

Definition move_one_ball_entail_wit_3 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) >= (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (move_one_ball_prefix_109 input_l (i + 1 ) num ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) >= (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_prefix_109 input_l (i + 1 ) num ) ”
  &&  emp
).

Definition move_one_ball_entail_wit_3_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth i input_l 0) >= (Znth (i - 1 ) input_l 0))) (PreH2 : (i < arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_prefix_109 input_l (i + 1 ) num ) ”
.

Definition move_one_ball_entail_wit_4_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_109_pre_z input_l )) (PreH5 : (move_one_ball_safe_109 input_l )) (PreH6 : (1 <= i)) (PreH7 : (i < arr_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= (i + 1 ))) (PreH10 : (move_one_ball_prefix_109 input_l (i + 1 ) num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= arr_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (move_one_ball_prefix_109 input_l (i + 1 ) num ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition move_one_ball_entail_wit_4_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (i: Z) (num: Z) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_109_pre_z input_l )) (PreH5 : (move_one_ball_safe_109 input_l )) (PreH6 : (1 <= i)) (PreH7 : (i < arr_size_pre)) (PreH8 : (0 <= num)) (PreH9 : (num <= i)) (PreH10 : (move_one_ball_prefix_109 input_l (i + 1 ) num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= arr_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= (i + 1 )) ” 
  &&  “ (move_one_ball_prefix_109 input_l (i + 1 ) num ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition move_one_ball_entail_wit_5_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) <= (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 < arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= arr_size_pre) ” 
  &&  “ (move_one_ball_wrap_109 input_l num ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) <= (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_wrap_109 input_l num ) ”
  &&  emp
).

Definition move_one_ball_entail_wit_5_1_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) <= (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_wrap_109 input_l num ) ”
.

Definition move_one_ball_entail_wit_5_2 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) > (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 < arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (0 <= (num + 1 )) ” 
  &&  “ ((num + 1 ) <= arr_size_pre) ” 
  &&  “ (move_one_ball_wrap_109 input_l (num + 1 ) ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) > (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_wrap_109 input_l (num + 1 ) ) ” 
  &&  “ ((num + 1 ) <= arr_size_pre) ”
  &&  emp
).

Definition move_one_ball_entail_wit_5_2_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) > (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ (move_one_ball_wrap_109 input_l (num + 1 ) ) ”
.

Definition move_one_ball_entail_wit_5_2_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : ((Znth (arr_size_pre - 1 ) input_l 0) > (Znth 0 input_l 0))) (PreH2 : (i >= arr_size_pre)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) (PreH8 : (1 <= i)) (PreH9 : (i <= arr_size_pre)) (PreH10 : (0 <= num)) (PreH11 : (num <= i)) (PreH12 : (move_one_ball_prefix_109 input_l i num )) ,
  TT && emp 
|--
  “ ((num + 1 ) <= arr_size_pre) ”
.

Definition move_one_ball_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (PreH1 : (num >= 2)) (PreH2 : (0 < arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (0 <= num)) (PreH8 : (num <= arr_size_pre)) (PreH9 : (move_one_ball_wrap_109 input_l num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  (“ (0 = 0) ” 
  &&  “ (problem_109_spec_z input_l false ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l ))
  ||
  (“ (0 <> 0) ” 
  &&  “ (problem_109_spec_z input_l true ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l ))
.

Definition move_one_ball_return_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (PreH1 : (num < 2)) (PreH2 : (0 < arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (0 <= num)) (PreH8 : (num <= arr_size_pre)) (PreH9 : (move_one_ball_wrap_109 input_l num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  (“ (1 = 0) ” 
  &&  “ (problem_109_spec_z input_l false ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l ))
  ||
  (“ (1 <> 0) ” 
  &&  “ (problem_109_spec_z input_l true ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l ))
.

Definition move_one_ball_return_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_size_pre = 0)) (PreH2 : (arr_pre <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_109_pre_z input_l )) (PreH7 : (move_one_ball_safe_109 input_l )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  (“ (1 = 0) ” 
  &&  “ (problem_109_spec_z input_l false ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l ))
  ||
  (“ (1 <> 0) ” 
  &&  “ (problem_109_spec_z input_l true ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l ))
.

Definition move_one_ball_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (i < arr_size_pre) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (move_one_ball_prefix_109 input_l i num ) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
.

Definition move_one_ball_partial_solve_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (i < arr_size_pre) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (move_one_ball_prefix_109 input_l i num ) ”
  &&  (((arr_pre + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (i - 1 ) input_l 0))
  **  (IntArray.missing_i arr_pre (i - 1 ) 0 arr_size_pre input_l )
.

Definition move_one_ball_partial_solve_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (i >= arr_size_pre) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (move_one_ball_prefix_109 input_l i num ) ”
  &&  (((arr_pre + ((arr_size_pre - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (arr_size_pre - 1 ) input_l 0))
  **  (IntArray.missing_i arr_pre (arr_size_pre - 1 ) 0 arr_size_pre input_l )
.

Definition move_one_ball_partial_solve_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_109_pre_z input_l )) (PreH6 : (move_one_ball_safe_109 input_l )) (PreH7 : (1 <= i)) (PreH8 : (i <= arr_size_pre)) (PreH9 : (0 <= num)) (PreH10 : (num <= i)) (PreH11 : (move_one_ball_prefix_109 input_l i num )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (i >= arr_size_pre) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_109_pre_z input_l ) ” 
  &&  “ (move_one_ball_safe_109 input_l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= i) ” 
  &&  “ (move_one_ball_prefix_109 input_l i num ) ”
  &&  (((arr_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 input_l 0))
  **  (IntArray.missing_i arr_pre 0 0 arr_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_move_one_ball_safety_wit_1 : move_one_ball_safety_wit_1.
Axiom proof_of_move_one_ball_safety_wit_2 : move_one_ball_safety_wit_2.
Axiom proof_of_move_one_ball_safety_wit_3 : move_one_ball_safety_wit_3.
Axiom proof_of_move_one_ball_safety_wit_4 : move_one_ball_safety_wit_4.
Axiom proof_of_move_one_ball_safety_wit_5 : move_one_ball_safety_wit_5.
Axiom proof_of_move_one_ball_safety_wit_6 : move_one_ball_safety_wit_6.
Axiom proof_of_move_one_ball_safety_wit_7 : move_one_ball_safety_wit_7.
Axiom proof_of_move_one_ball_safety_wit_8 : move_one_ball_safety_wit_8.
Axiom proof_of_move_one_ball_safety_wit_9 : move_one_ball_safety_wit_9.
Axiom proof_of_move_one_ball_safety_wit_10 : move_one_ball_safety_wit_10.
Axiom proof_of_move_one_ball_safety_wit_11 : move_one_ball_safety_wit_11.
Axiom proof_of_move_one_ball_safety_wit_12 : move_one_ball_safety_wit_12.
Axiom proof_of_move_one_ball_safety_wit_13 : move_one_ball_safety_wit_13.
Axiom proof_of_move_one_ball_safety_wit_14 : move_one_ball_safety_wit_14.
Axiom proof_of_move_one_ball_safety_wit_15 : move_one_ball_safety_wit_15.
Axiom proof_of_move_one_ball_safety_wit_16 : move_one_ball_safety_wit_16.
Axiom proof_of_move_one_ball_safety_wit_17 : move_one_ball_safety_wit_17.
Axiom proof_of_move_one_ball_safety_wit_18 : move_one_ball_safety_wit_18.
Axiom proof_of_move_one_ball_entail_wit_1 : move_one_ball_entail_wit_1.
Axiom proof_of_move_one_ball_entail_wit_2 : move_one_ball_entail_wit_2.
Axiom proof_of_move_one_ball_entail_wit_3 : move_one_ball_entail_wit_3.
Axiom proof_of_move_one_ball_entail_wit_4_1 : move_one_ball_entail_wit_4_1.
Axiom proof_of_move_one_ball_entail_wit_4_2 : move_one_ball_entail_wit_4_2.
Axiom proof_of_move_one_ball_entail_wit_5_1 : move_one_ball_entail_wit_5_1.
Axiom proof_of_move_one_ball_entail_wit_5_2 : move_one_ball_entail_wit_5_2.
Axiom proof_of_move_one_ball_return_wit_1 : move_one_ball_return_wit_1.
Axiom proof_of_move_one_ball_return_wit_2 : move_one_ball_return_wit_2.
Axiom proof_of_move_one_ball_return_wit_3 : move_one_ball_return_wit_3.
Axiom proof_of_move_one_ball_partial_solve_wit_1 : move_one_ball_partial_solve_wit_1.
Axiom proof_of_move_one_ball_partial_solve_wit_2 : move_one_ball_partial_solve_wit_2.
Axiom proof_of_move_one_ball_partial_solve_wit_3 : move_one_ball_partial_solve_wit_3.
Axiom proof_of_move_one_ball_partial_solve_wit_4 : move_one_ball_partial_solve_wit_4.

End VC_Correct.
