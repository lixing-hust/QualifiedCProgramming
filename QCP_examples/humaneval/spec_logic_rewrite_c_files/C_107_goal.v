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
Require Import coins_107.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function is_pal -----*)

Definition is_pal_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (int_range_107 x_pre )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_pal_safety_wit_2 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (int_range_107 x_pre )) (PreH2 : (0 <= t)) (PreH3 : (t <= x_pre)) (PreH4 : (0 <= r)) (PreH5 : (r <= 9999)) (PreH6 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_pal_safety_wit_3 := 
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (((r * 10 ) + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((r * 10 ) + (t % ( 10 ) ) )) ”
) \/
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (((r * 10 ) + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((r * 10 ) + (t % ( 10 ) ) )) ”
).

Definition is_pal_safety_wit_3_split_goal_1 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (((r * 10 ) + (t % ( 10 ) ) ) <= INT_MAX) ”
.

Definition is_pal_safety_wit_3_split_goal_2 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((INT_MIN) <= ((r * 10 ) + (t % ( 10 ) ) )) ”
.

Definition is_pal_safety_wit_4 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition is_pal_safety_wit_5 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r * 10 )) ”
.

Definition is_pal_safety_wit_6 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition is_pal_safety_wit_7 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition is_pal_safety_wit_8 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> ((r * 10 ) + (t % ( 10 ) ) ))
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition is_pal_safety_wit_9 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "r" ) )) # Int  |-> ((r * 10 ) + (t % ( 10 ) ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition is_pal_entail_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (int_range_107 x_pre )) ,
  TT && emp 
|--
  “ (int_range_107 x_pre ) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= x_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 9999) ” 
  &&  “ (pal_scan_state_107 x_pre x_pre 0 ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (int_range_107 x_pre )) ,
  TT && emp 
|--
  “ (pal_scan_state_107 x_pre x_pre 0 ) ” 
  &&  “ (0 <= x_pre) ”
  &&  emp
).

Definition is_pal_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (int_range_107 x_pre )) ,
  TT && emp 
|--
  “ (pal_scan_state_107 x_pre x_pre 0 ) ”
.

Definition is_pal_entail_wit_1_split_goal_2 := 
forall (x_pre: Z) (PreH1 : (int_range_107 x_pre )) ,
  TT && emp 
|--
  “ (0 <= x_pre) ”
.

Definition is_pal_entail_wit_2 := 
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (int_range_107 x_pre ) ” 
  &&  “ (0 <= (t ÷ 10 )) ” 
  &&  “ ((t ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= ((r * 10 ) + (t % ( 10 ) ) )) ” 
  &&  “ (((r * 10 ) + (t % ( 10 ) ) ) <= 9999) ” 
  &&  “ (pal_scan_state_107 x_pre (t ÷ 10 ) ((r * 10 ) + (t % ( 10 ) ) ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (pal_scan_state_107 x_pre (t ÷ 10 ) ((r * 10 ) + (t % ( 10 ) ) ) ) ” 
  &&  “ (((r * 10 ) + (t % ( 10 ) ) ) <= 9999) ” 
  &&  “ (0 <= ((r * 10 ) + (t % ( 10 ) ) )) ” 
  &&  “ ((t ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= (t ÷ 10 )) ”
  &&  emp
).

Definition is_pal_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (pal_scan_state_107 x_pre (t ÷ 10 ) ((r * 10 ) + (t % ( 10 ) ) ) ) ”
.

Definition is_pal_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (((r * 10 ) + (t % ( 10 ) ) ) <= 9999) ”
.

Definition is_pal_entail_wit_2_split_goal_3 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (0 <= ((r * 10 ) + (t % ( 10 ) ) )) ”
.

Definition is_pal_entail_wit_2_split_goal_4 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ ((t ÷ 10 ) <= x_pre) ”
.

Definition is_pal_entail_wit_2_split_goal_5 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (int_range_107 x_pre )) (PreH3 : (0 <= t)) (PreH4 : (t <= x_pre)) (PreH5 : (0 <= r)) (PreH6 : (r <= 9999)) (PreH7 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (0 <= (t ÷ 10 )) ”
.

Definition is_pal_return_wit_1 := 
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (r <> x_pre)) (PreH2 : (t <= 0)) (PreH3 : (int_range_107 x_pre )) (PreH4 : (0 <= t)) (PreH5 : (t <= x_pre)) (PreH6 : (0 <= r)) (PreH7 : (r <= 9999)) (PreH8 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (0 = (is_pal_result_107 (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (r <> x_pre)) (PreH2 : (t <= 0)) (PreH3 : (int_range_107 x_pre )) (PreH4 : (0 <= t)) (PreH5 : (t <= x_pre)) (PreH6 : (0 <= r)) (PreH7 : (r <= 9999)) (PreH8 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (0 = (is_pal_result_107 (x_pre))) ”
  &&  emp
).

Definition is_pal_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (r <> x_pre)) (PreH2 : (t <= 0)) (PreH3 : (int_range_107 x_pre )) (PreH4 : (0 <= t)) (PreH5 : (t <= x_pre)) (PreH6 : (0 <= r)) (PreH7 : (r <= 9999)) (PreH8 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (0 = (is_pal_result_107 (x_pre))) ”
.

Definition is_pal_return_wit_2 := 
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (r = x_pre)) (PreH2 : (t <= 0)) (PreH3 : (int_range_107 x_pre )) (PreH4 : (0 <= t)) (PreH5 : (t <= x_pre)) (PreH6 : (0 <= r)) (PreH7 : (r <= 9999)) (PreH8 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (1 = (is_pal_result_107 (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (r = x_pre)) (PreH2 : (t <= 0)) (PreH3 : (int_range_107 x_pre )) (PreH4 : (0 <= t)) (PreH5 : (t <= x_pre)) (PreH6 : (0 <= r)) (PreH7 : (r <= 9999)) (PreH8 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (1 = (is_pal_result_107 (x_pre))) ”
  &&  emp
).

Definition is_pal_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (r: Z) (t: Z) (PreH1 : (r = x_pre)) (PreH2 : (t <= 0)) (PreH3 : (int_range_107 x_pre )) (PreH4 : (0 <= t)) (PreH5 : (t <= x_pre)) (PreH6 : (0 <= r)) (PreH7 : (r <= 9999)) (PreH8 : (pal_scan_state_107 x_pre t r )) ,
  TT && emp 
|--
  “ (1 = (is_pal_result_107 (x_pre))) ”
.

(*----- Function even_odd_palindrome -----*)

Definition even_odd_palindrome_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) ,
  ((( &( "num2" ) )) # Int  |->_)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_palindrome_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) ,
  ((( &( "num1" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_palindrome_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (problem_107_pre_z n0 )) (PreH4 : (int_range_107 n0 )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_palindrome_safety_wit_4 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_palindrome_safety_wit_5 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (is_pal_result_107 (i)))) (PreH3 : (i <= n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= (i - 1 ))) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= (i - 1 ))) (PreH12 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH13 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition even_odd_palindrome_safety_wit_6 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (is_pal_result_107 (i)))) (PreH3 : (i <= n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= (i - 1 ))) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= (i - 1 ))) (PreH12 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH13 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_palindrome_safety_wit_7 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (is_pal_result_107 (i)))) (PreH3 : (i <= n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= (i - 1 ))) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= (i - 1 ))) (PreH12 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH13 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_palindrome_safety_wit_8 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : ((i % ( 2 ) ) = 1)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (is_pal_result_107 (i)))) (PreH4 : (i <= n0)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= (i - 1 ))) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= (i - 1 ))) (PreH13 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH14 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((num1 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num1 + 1 )) ”
.

Definition even_odd_palindrome_safety_wit_9 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : ((i % ( 2 ) ) = 1)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (is_pal_result_107 (i)))) (PreH4 : (i <= n0)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= (i - 1 ))) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= (i - 1 ))) (PreH13 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH14 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_palindrome_safety_wit_10 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition even_odd_palindrome_safety_wit_11 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition even_odd_palindrome_safety_wit_12 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) <> 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition even_odd_palindrome_safety_wit_13 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) <> 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_palindrome_safety_wit_14 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_palindrome_safety_wit_15 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_palindrome_safety_wit_16 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) <> 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_palindrome_safety_wit_17 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_palindrome_safety_wit_18 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_palindrome_safety_wit_19 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : (retval = 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ False ”
.

Definition even_odd_palindrome_safety_wit_20 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : (retval = 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ False ”
.

Definition even_odd_palindrome_safety_wit_21 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ False ”
.

Definition even_odd_palindrome_safety_wit_22 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) <> 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ False ”
.

Definition even_odd_palindrome_safety_wit_23 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ False ”
.

Definition even_odd_palindrome_safety_wit_24 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((num2 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num2 + 1 )) ”
.

Definition even_odd_palindrome_safety_wit_25 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_palindrome_safety_wit_26 := 
(
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition even_odd_palindrome_safety_wit_26_split_goal_1 := 
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition even_odd_palindrome_safety_wit_26_split_goal_2 := 
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition even_odd_palindrome_safety_wit_27 := 
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> (n0 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_palindrome_safety_wit_28 := 
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> (n0 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_palindrome_safety_wit_29 := 
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) ,
  (((data + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  (IntArray.undef_seg data 1 2 )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> (n0 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_palindrome_entail_wit_1 := 
(
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) ,
  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n0 + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (1 - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (1 - 1 )) ” 
  &&  “ (0 = (count_odd_pal_prefix_107 ((1 - 1 )))) ” 
  &&  “ (0 = (count_even_pal_prefix_107 ((1 - 1 )))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full retval_2 2 )
) \/
(
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) ,
  (IntArray.undef_full retval_2 2 )
|--
  “ (0 = (count_even_pal_prefix_107 ((1 - 1 )))) ” 
  &&  “ (0 = (count_odd_pal_prefix_107 ((1 - 1 )))) ” 
  &&  “ (1 <= (n0 + 1 )) ”
  &&  (IntArray.undef_full retval_2 2 )
).

Definition even_odd_palindrome_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) ,
  (IntArray.undef_full retval_2 2 )
|--
  “ (0 = (count_even_pal_prefix_107 ((1 - 1 )))) ”
.

Definition even_odd_palindrome_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) ,
  (IntArray.undef_full retval_2 2 )
|--
  “ (0 = (count_odd_pal_prefix_107 ((1 - 1 )))) ”
.

Definition even_odd_palindrome_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) ,
  (IntArray.undef_full retval_2 2 )
|--
  “ (1 <= (n0 + 1 )) ”
.

Definition even_odd_palindrome_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) ,
  (IntArray.undef_full retval_2 2 )
|--
  (IntArray.undef_full retval_2 2 )
.

Definition even_odd_palindrome_entail_wit_2_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) <> 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_result_107 (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (retval_3: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
.

Definition even_odd_palindrome_entail_wit_2_2 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  (“ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_result_107 (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (retval_3: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (retval_4: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
.

Definition even_odd_palindrome_entail_wit_2_3 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (is_pal_result_107 (i)))) (PreH3 : ((i % ( 2 ) ) = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (is_pal_result_107 (i)))) (PreH6 : (i <= n0)) (PreH7 : (problem_107_pre_z n0 )) (PreH8 : (int_range_107 n0 )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n0 + 1 ))) (PreH11 : (0 <= num1)) (PreH12 : (num1 <= (i - 1 ))) (PreH13 : (0 <= num2)) (PreH14 : (num2 <= (i - 1 ))) (PreH15 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH16 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_result_107 (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= (num1 + 1 )) ” 
  &&  “ ((num1 + 1 ) <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ ((num1 + 1 ) = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (retval_4: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= (num1 + 1 )) ” 
  &&  “ ((num1 + 1 ) <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ ((num1 + 1 ) = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
.

Definition even_odd_palindrome_entail_wit_2_4 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_3: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_3 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_result_107 (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= (num1 + 1 )) ” 
  &&  “ ((num1 + 1 ) <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ ((num1 + 1 ) = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (retval_4: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= (num1 + 1 )) ” 
  &&  “ ((num1 + 1 ) <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ ((num1 + 1 ) = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
.

Definition even_odd_palindrome_entail_wit_2_5 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_4: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_4 <> 0)) (PreH3 : (retval_4 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_result_107 (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (retval_3: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
  ||
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (is_pal_result_107 (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 ))
.

Definition even_odd_palindrome_entail_wit_3_1 := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= i) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= i) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (i))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (i))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (i))) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (i))) ”
  &&  (IntArray.undef_full data 2 )
).

Definition even_odd_palindrome_entail_wit_3_1_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_1_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num1 = (count_odd_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_1_split_goal_spatial := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_entail_wit_3_2 := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (0 <= (num1 + 1 )) ” 
  &&  “ ((num1 + 1 ) <= i) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= i) ” 
  &&  “ ((num1 + 1 ) = (count_odd_pal_prefix_107 (i))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (i))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (i))) ” 
  &&  “ ((num1 + 1 ) = (count_odd_pal_prefix_107 (i))) ”
  &&  (IntArray.undef_full data 2 )
).

Definition even_odd_palindrome_entail_wit_3_2_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_2_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ ((num1 + 1 ) = (count_odd_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_2_split_goal_spatial := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_entail_wit_3_3 := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= i) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= i) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (i))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (i))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (i))) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (i))) ”
  &&  (IntArray.undef_full data 2 )
).

Definition even_odd_palindrome_entail_wit_3_3_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_3_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num1 = (count_odd_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_3_split_goal_spatial := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (is_pal_result_107 (i)))) (PreH3 : (retval = 0)) (PreH4 : (retval = (is_pal_result_107 (i)))) (PreH5 : (i <= n0)) (PreH6 : (problem_107_pre_z n0 )) (PreH7 : (int_range_107 n0 )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (0 <= num1)) (PreH11 : (num1 <= (i - 1 ))) (PreH12 : (0 <= num2)) (PreH13 : (num2 <= (i - 1 ))) (PreH14 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH15 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_entail_wit_3_4 := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= i) ” 
  &&  “ (0 <= (num2 + 1 )) ” 
  &&  “ ((num2 + 1 ) <= i) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (i))) ” 
  &&  “ ((num2 + 1 ) = (count_even_pal_prefix_107 (i))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ ((num2 + 1 ) = (count_even_pal_prefix_107 (i))) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (i))) ”
  &&  (IntArray.undef_full data 2 )
).

Definition even_odd_palindrome_entail_wit_3_4_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ ((num2 + 1 ) = (count_even_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_4_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num1 = (count_odd_pal_prefix_107 (i))) ”
.

Definition even_odd_palindrome_entail_wit_3_4_split_goal_spatial := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (is_pal_result_107 (i)))) (PreH4 : ((i % ( 2 ) ) <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (is_pal_result_107 (i)))) (PreH7 : (i <= n0)) (PreH8 : (problem_107_pre_z n0 )) (PreH9 : (int_range_107 n0 )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n0 + 1 ))) (PreH12 : (0 <= num1)) (PreH13 : (num1 <= (i - 1 ))) (PreH14 : (0 <= num2)) (PreH15 : (num2 <= (i - 1 ))) (PreH16 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH17 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_entail_wit_4 := 
(
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= ((i + 1 ) - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= ((i + 1 ) - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (((i + 1 ) - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (((i + 1 ) - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
) \/
(
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (((i + 1 ) - 1 )))) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (((i + 1 ) - 1 )))) ”
  &&  (IntArray.undef_full data 2 )
).

Definition even_odd_palindrome_entail_wit_4_split_goal_1 := 
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (((i + 1 ) - 1 )))) ”
.

Definition even_odd_palindrome_entail_wit_4_split_goal_2 := 
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num1 = (count_odd_pal_prefix_107 (((i + 1 ) - 1 )))) ”
.

Definition even_odd_palindrome_entail_wit_4_split_goal_spatial := 
forall (n0: Z) (i: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (1 <= i)) (PreH4 : (i <= n0)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= i)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= i)) (PreH9 : (num1 = (count_odd_pal_prefix_107 (i)))) (PreH10 : (num2 = (count_even_pal_prefix_107 (i)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_entail_wit_5 := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) (PreH4 : (1 <= i)) (PreH5 : (i <= (n0 + 1 ))) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= (i - 1 ))) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= (i - 1 ))) (PreH10 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH11 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (n0))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (n0))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((( &( "i" ) )) # Int  |-> (n0 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) (PreH4 : (1 <= i)) (PreH5 : (i <= (n0 + 1 ))) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= (i - 1 ))) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= (i - 1 ))) (PreH10 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH11 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (n0))) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (n0))) ”
  &&  (IntArray.undef_full data 2 )
).

Definition even_odd_palindrome_entail_wit_5_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) (PreH4 : (1 <= i)) (PreH5 : (i <= (n0 + 1 ))) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= (i - 1 ))) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= (i - 1 ))) (PreH10 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH11 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num2 = (count_even_pal_prefix_107 (n0))) ”
.

Definition even_odd_palindrome_entail_wit_5_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) (PreH4 : (1 <= i)) (PreH5 : (i <= (n0 + 1 ))) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= (i - 1 ))) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= (i - 1 ))) (PreH10 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH11 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  “ (num1 = (count_odd_pal_prefix_107 (n0))) ”
.

Definition even_odd_palindrome_entail_wit_5_split_goal_spatial := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) (PreH4 : (1 <= i)) (PreH5 : (i <= (n0 + 1 ))) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= (i - 1 ))) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= (i - 1 ))) (PreH10 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH11 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  (IntArray.undef_full data 2 )
|--
  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_entail_wit_6 := 
(
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) ,
  (((data + (1 * sizeof(INT) ) )) # Int  |-> num1)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (n0))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (n0))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 (cons (num2) ((cons (num1) ((@nil Z))))) )
) \/
(
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (num2 >= INT_MIN)) (PreH4 : (num1 >= INT_MIN)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH8 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  (((data + (1 * sizeof(INT) ) )) # Int  |-> num1)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> num2)
|--
  (IntArray.full data 2 (cons (num2) ((cons (num1) ((@nil Z))))) )
).

Definition even_odd_palindrome_entail_wit_6_split_goal_spatial := 
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (num2 >= INT_MIN)) (PreH4 : (num1 >= INT_MIN)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH8 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  (((data + (1 * sizeof(INT) ) )) # Int  |-> num1)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> num2)
|--
  (IntArray.full data 2 (cons (num2) ((cons (num1) ((@nil Z))))) )
.

Definition even_odd_palindrome_return_wit_1 := 
(
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data_2: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data_2 2 (cons (num2) ((cons (num1) ((@nil Z))))) )
|--
  EX (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_107_spec_z n0 (cons ((count_even_pal_prefix_107 (n0))) ((cons ((count_odd_pal_prefix_107 (n0))) ((@nil Z))))) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 (cons ((count_even_pal_prefix_107 (n0))) ((cons ((count_odd_pal_prefix_107 (n0))) ((@nil Z))))) )
) \/
(
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data_2: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) ,
  TT && emp 
|--
  “ (problem_107_spec_z n0 (cons ((count_even_pal_prefix_107 (n0))) ((cons ((count_odd_pal_prefix_107 (n0))) ((@nil Z))))) ) ”
  &&  emp
).

Definition even_odd_palindrome_return_wit_1_split_goal_1 := 
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data_2: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) ,
  TT && emp 
|--
  “ (problem_107_spec_z n0 (cons ((count_even_pal_prefix_107 (n0))) ((cons ((count_odd_pal_prefix_107 (n0))) ((@nil Z))))) ) ”
.

Definition even_odd_palindrome_partial_solve_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) ,
  TT && emp 
|--
  “ (n_pre = n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ”
  &&  emp
.

Definition even_odd_palindrome_partial_solve_wit_2_pure := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (problem_107_pre_z n0 )) (PreH4 : (int_range_107 n0 )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 >= 0) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition even_odd_palindrome_partial_solve_wit_2_aux := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (problem_107_pre_z n0 )) (PreH4 : (int_range_107 n0 )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 >= 0) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition even_odd_palindrome_partial_solve_wit_2 := even_odd_palindrome_partial_solve_wit_2_pure -> even_odd_palindrome_partial_solve_wit_2_aux.

Definition even_odd_palindrome_partial_solve_wit_3_pure := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) (PreH4 : (1 <= i)) (PreH5 : (i <= (n0 + 1 ))) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= (i - 1 ))) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= (i - 1 ))) (PreH10 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH11 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : (num1 >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : (i <= n0)) (PreH10 : (problem_107_pre_z n0 )) (PreH11 : (int_range_107 n0 )) (PreH12 : (1 <= i)) (PreH13 : (i <= (n0 + 1 ))) (PreH14 : (0 <= num1)) (PreH15 : (num1 <= (i - 1 ))) (PreH16 : (0 <= num2)) (PreH17 : (num2 <= (i - 1 ))) (PreH18 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH19 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
).

Definition even_odd_palindrome_partial_solve_wit_3_pure_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : (num1 >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : (i <= n0)) (PreH10 : (problem_107_pre_z n0 )) (PreH11 : (int_range_107 n0 )) (PreH12 : (1 <= i)) (PreH13 : (i <= (n0 + 1 ))) (PreH14 : (0 <= num1)) (PreH15 : (num1 <= (i - 1 ))) (PreH16 : (0 <= num2)) (PreH17 : (num2 <= (i - 1 ))) (PreH18 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH19 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
.

Definition even_odd_palindrome_partial_solve_wit_3_aux := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (problem_107_pre_z n0 )) (PreH3 : (int_range_107 n0 )) (PreH4 : (1 <= i)) (PreH5 : (i <= (n0 + 1 ))) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= (i - 1 ))) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= (i - 1 ))) (PreH10 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH11 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_partial_solve_wit_3 := even_odd_palindrome_partial_solve_wit_3_pure -> even_odd_palindrome_partial_solve_wit_3_aux.

Definition even_odd_palindrome_partial_solve_wit_4_pure := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : ((i % ( 2 ) ) = 1)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (is_pal_result_107 (i)))) (PreH4 : (i <= n0)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= (i - 1 ))) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= (i - 1 ))) (PreH13 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH14 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : ((num1 + 1 ) <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : ((num1 + 1 ) >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : ((i % ( 2 ) ) = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (is_pal_result_107 (i)))) (PreH12 : (i <= n0)) (PreH13 : (problem_107_pre_z n0 )) (PreH14 : (int_range_107 n0 )) (PreH15 : (1 <= i)) (PreH16 : (i <= (n0 + 1 ))) (PreH17 : (0 <= num1)) (PreH18 : (num1 <= (i - 1 ))) (PreH19 : (0 <= num2)) (PreH20 : (num2 <= (i - 1 ))) (PreH21 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH22 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH23 : (out <> 0)) (PreH24 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
).

Definition even_odd_palindrome_partial_solve_wit_4_pure_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : ((num1 + 1 ) <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : ((num1 + 1 ) >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : ((i % ( 2 ) ) = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (is_pal_result_107 (i)))) (PreH12 : (i <= n0)) (PreH13 : (problem_107_pre_z n0 )) (PreH14 : (int_range_107 n0 )) (PreH15 : (1 <= i)) (PreH16 : (i <= (n0 + 1 ))) (PreH17 : (0 <= num1)) (PreH18 : (num1 <= (i - 1 ))) (PreH19 : (0 <= num2)) (PreH20 : (num2 <= (i - 1 ))) (PreH21 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH22 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH23 : (out <> 0)) (PreH24 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
.

Definition even_odd_palindrome_partial_solve_wit_4_aux := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : ((i % ( 2 ) ) = 1)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (is_pal_result_107 (i)))) (PreH4 : (i <= n0)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= (i - 1 ))) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= (i - 1 ))) (PreH13 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH14 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_partial_solve_wit_4 := even_odd_palindrome_partial_solve_wit_4_pure -> even_odd_palindrome_partial_solve_wit_4_aux.

Definition even_odd_palindrome_partial_solve_wit_5_pure := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (is_pal_result_107 (i)))) (PreH3 : (i <= n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= (i - 1 ))) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= (i - 1 ))) (PreH12 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH13 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : (num1 >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : (retval = 0)) (PreH10 : (retval = (is_pal_result_107 (i)))) (PreH11 : (i <= n0)) (PreH12 : (problem_107_pre_z n0 )) (PreH13 : (int_range_107 n0 )) (PreH14 : (1 <= i)) (PreH15 : (i <= (n0 + 1 ))) (PreH16 : (0 <= num1)) (PreH17 : (num1 <= (i - 1 ))) (PreH18 : (0 <= num2)) (PreH19 : (num2 <= (i - 1 ))) (PreH20 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH21 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH22 : (out <> 0)) (PreH23 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
).

Definition even_odd_palindrome_partial_solve_wit_5_pure_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : (num1 >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : (retval = 0)) (PreH10 : (retval = (is_pal_result_107 (i)))) (PreH11 : (i <= n0)) (PreH12 : (problem_107_pre_z n0 )) (PreH13 : (int_range_107 n0 )) (PreH14 : (1 <= i)) (PreH15 : (i <= (n0 + 1 ))) (PreH16 : (0 <= num1)) (PreH17 : (num1 <= (i - 1 ))) (PreH18 : (0 <= num2)) (PreH19 : (num2 <= (i - 1 ))) (PreH20 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH21 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH22 : (out <> 0)) (PreH23 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
.

Definition even_odd_palindrome_partial_solve_wit_5_aux := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (is_pal_result_107 (i)))) (PreH3 : (i <= n0)) (PreH4 : (problem_107_pre_z n0 )) (PreH5 : (int_range_107 n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= (i - 1 ))) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= (i - 1 ))) (PreH12 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH13 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_partial_solve_wit_5 := even_odd_palindrome_partial_solve_wit_5_pure -> even_odd_palindrome_partial_solve_wit_5_aux.

Definition even_odd_palindrome_partial_solve_wit_6_pure := 
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : ((i % ( 2 ) ) <> 1)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (is_pal_result_107 (i)))) (PreH4 : (i <= n0)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= (i - 1 ))) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= (i - 1 ))) (PreH13 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH14 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : (num1 >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : ((i % ( 2 ) ) <> 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (is_pal_result_107 (i)))) (PreH12 : (i <= n0)) (PreH13 : (problem_107_pre_z n0 )) (PreH14 : (int_range_107 n0 )) (PreH15 : (1 <= i)) (PreH16 : (i <= (n0 + 1 ))) (PreH17 : (0 <= num1)) (PreH18 : (num1 <= (i - 1 ))) (PreH19 : (0 <= num2)) (PreH20 : (num2 <= (i - 1 ))) (PreH21 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH22 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH23 : (out <> 0)) (PreH24 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
).

Definition even_odd_palindrome_partial_solve_wit_6_pure_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num2 <= INT_MAX)) (PreH2 : (num1 <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n0 <= INT_MAX)) (PreH5 : (num2 >= INT_MIN)) (PreH6 : (num1 >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n0 >= INT_MIN)) (PreH9 : ((i % ( 2 ) ) <> 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (is_pal_result_107 (i)))) (PreH12 : (i <= n0)) (PreH13 : (problem_107_pre_z n0 )) (PreH14 : (int_range_107 n0 )) (PreH15 : (1 <= i)) (PreH16 : (i <= (n0 + 1 ))) (PreH17 : (0 <= num1)) (PreH18 : (num1 <= (i - 1 ))) (PreH19 : (0 <= num2)) (PreH20 : (num2 <= (i - 1 ))) (PreH21 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH22 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH23 : (out <> 0)) (PreH24 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ”
.

Definition even_odd_palindrome_partial_solve_wit_6_aux := 
forall (n0: Z) (data: Z) (out: Z) (num2: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : ((i % ( 2 ) ) <> 1)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (is_pal_result_107 (i)))) (PreH4 : (i <= n0)) (PreH5 : (problem_107_pre_z n0 )) (PreH6 : (int_range_107 n0 )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= (i - 1 ))) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= (i - 1 ))) (PreH13 : (num1 = (count_odd_pal_prefix_107 ((i - 1 ))))) (PreH14 : (num2 = (count_even_pal_prefix_107 ((i - 1 ))))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
|--
  “ (int_range_107 i ) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_result_107 (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= (i - 1 )) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= (i - 1 )) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 ((i - 1 )))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.undef_full data 2 )
.

Definition even_odd_palindrome_partial_solve_wit_6 := even_odd_palindrome_partial_solve_wit_6_pure -> even_odd_palindrome_partial_solve_wit_6_aux.

Definition even_odd_palindrome_partial_solve_wit_7 := 
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.undef_full data 2 )
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (n0))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (n0))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data 1 2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition even_odd_palindrome_partial_solve_wit_8 := 
forall (n0: Z) (num1: Z) (num2: Z) (out: Z) (data: Z) (PreH1 : (problem_107_pre_z n0 )) (PreH2 : (int_range_107 n0 )) (PreH3 : (num1 = (count_odd_pal_prefix_107 (n0)))) (PreH4 : (num2 = (count_even_pal_prefix_107 (n0)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) ,
  (((data + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  (IntArray.undef_seg data 1 2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (problem_107_pre_z n0 ) ” 
  &&  “ (int_range_107 n0 ) ” 
  &&  “ (num1 = (count_odd_pal_prefix_107 (n0))) ” 
  &&  “ (num2 = (count_even_pal_prefix_107 (n0))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_is_pal_safety_wit_1 : is_pal_safety_wit_1.
Axiom proof_of_is_pal_safety_wit_2 : is_pal_safety_wit_2.
Axiom proof_of_is_pal_safety_wit_3 : is_pal_safety_wit_3.
Axiom proof_of_is_pal_safety_wit_4 : is_pal_safety_wit_4.
Axiom proof_of_is_pal_safety_wit_5 : is_pal_safety_wit_5.
Axiom proof_of_is_pal_safety_wit_6 : is_pal_safety_wit_6.
Axiom proof_of_is_pal_safety_wit_7 : is_pal_safety_wit_7.
Axiom proof_of_is_pal_safety_wit_8 : is_pal_safety_wit_8.
Axiom proof_of_is_pal_safety_wit_9 : is_pal_safety_wit_9.
Axiom proof_of_is_pal_entail_wit_1 : is_pal_entail_wit_1.
Axiom proof_of_is_pal_entail_wit_2 : is_pal_entail_wit_2.
Axiom proof_of_is_pal_return_wit_1 : is_pal_return_wit_1.
Axiom proof_of_is_pal_return_wit_2 : is_pal_return_wit_2.
Axiom proof_of_even_odd_palindrome_safety_wit_1 : even_odd_palindrome_safety_wit_1.
Axiom proof_of_even_odd_palindrome_safety_wit_2 : even_odd_palindrome_safety_wit_2.
Axiom proof_of_even_odd_palindrome_safety_wit_3 : even_odd_palindrome_safety_wit_3.
Axiom proof_of_even_odd_palindrome_safety_wit_4 : even_odd_palindrome_safety_wit_4.
Axiom proof_of_even_odd_palindrome_safety_wit_5 : even_odd_palindrome_safety_wit_5.
Axiom proof_of_even_odd_palindrome_safety_wit_6 : even_odd_palindrome_safety_wit_6.
Axiom proof_of_even_odd_palindrome_safety_wit_7 : even_odd_palindrome_safety_wit_7.
Axiom proof_of_even_odd_palindrome_safety_wit_8 : even_odd_palindrome_safety_wit_8.
Axiom proof_of_even_odd_palindrome_safety_wit_9 : even_odd_palindrome_safety_wit_9.
Axiom proof_of_even_odd_palindrome_safety_wit_10 : even_odd_palindrome_safety_wit_10.
Axiom proof_of_even_odd_palindrome_safety_wit_11 : even_odd_palindrome_safety_wit_11.
Axiom proof_of_even_odd_palindrome_safety_wit_12 : even_odd_palindrome_safety_wit_12.
Axiom proof_of_even_odd_palindrome_safety_wit_13 : even_odd_palindrome_safety_wit_13.
Axiom proof_of_even_odd_palindrome_safety_wit_14 : even_odd_palindrome_safety_wit_14.
Axiom proof_of_even_odd_palindrome_safety_wit_15 : even_odd_palindrome_safety_wit_15.
Axiom proof_of_even_odd_palindrome_safety_wit_16 : even_odd_palindrome_safety_wit_16.
Axiom proof_of_even_odd_palindrome_safety_wit_17 : even_odd_palindrome_safety_wit_17.
Axiom proof_of_even_odd_palindrome_safety_wit_18 : even_odd_palindrome_safety_wit_18.
Axiom proof_of_even_odd_palindrome_safety_wit_19 : even_odd_palindrome_safety_wit_19.
Axiom proof_of_even_odd_palindrome_safety_wit_20 : even_odd_palindrome_safety_wit_20.
Axiom proof_of_even_odd_palindrome_safety_wit_21 : even_odd_palindrome_safety_wit_21.
Axiom proof_of_even_odd_palindrome_safety_wit_22 : even_odd_palindrome_safety_wit_22.
Axiom proof_of_even_odd_palindrome_safety_wit_23 : even_odd_palindrome_safety_wit_23.
Axiom proof_of_even_odd_palindrome_safety_wit_24 : even_odd_palindrome_safety_wit_24.
Axiom proof_of_even_odd_palindrome_safety_wit_25 : even_odd_palindrome_safety_wit_25.
Axiom proof_of_even_odd_palindrome_safety_wit_26 : even_odd_palindrome_safety_wit_26.
Axiom proof_of_even_odd_palindrome_safety_wit_27 : even_odd_palindrome_safety_wit_27.
Axiom proof_of_even_odd_palindrome_safety_wit_28 : even_odd_palindrome_safety_wit_28.
Axiom proof_of_even_odd_palindrome_safety_wit_29 : even_odd_palindrome_safety_wit_29.
Axiom proof_of_even_odd_palindrome_entail_wit_1 : even_odd_palindrome_entail_wit_1.
Axiom proof_of_even_odd_palindrome_entail_wit_2_1 : even_odd_palindrome_entail_wit_2_1.
Axiom proof_of_even_odd_palindrome_entail_wit_2_2 : even_odd_palindrome_entail_wit_2_2.
Axiom proof_of_even_odd_palindrome_entail_wit_2_3 : even_odd_palindrome_entail_wit_2_3.
Axiom proof_of_even_odd_palindrome_entail_wit_2_4 : even_odd_palindrome_entail_wit_2_4.
Axiom proof_of_even_odd_palindrome_entail_wit_2_5 : even_odd_palindrome_entail_wit_2_5.
Axiom proof_of_even_odd_palindrome_entail_wit_3_1 : even_odd_palindrome_entail_wit_3_1.
Axiom proof_of_even_odd_palindrome_entail_wit_3_2 : even_odd_palindrome_entail_wit_3_2.
Axiom proof_of_even_odd_palindrome_entail_wit_3_3 : even_odd_palindrome_entail_wit_3_3.
Axiom proof_of_even_odd_palindrome_entail_wit_3_4 : even_odd_palindrome_entail_wit_3_4.
Axiom proof_of_even_odd_palindrome_entail_wit_4 : even_odd_palindrome_entail_wit_4.
Axiom proof_of_even_odd_palindrome_entail_wit_5 : even_odd_palindrome_entail_wit_5.
Axiom proof_of_even_odd_palindrome_entail_wit_6 : even_odd_palindrome_entail_wit_6.
Axiom proof_of_even_odd_palindrome_return_wit_1 : even_odd_palindrome_return_wit_1.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_1 : even_odd_palindrome_partial_solve_wit_1.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_2_pure : even_odd_palindrome_partial_solve_wit_2_pure.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_2 : even_odd_palindrome_partial_solve_wit_2.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_3_pure : even_odd_palindrome_partial_solve_wit_3_pure.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_3 : even_odd_palindrome_partial_solve_wit_3.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_4_pure : even_odd_palindrome_partial_solve_wit_4_pure.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_4 : even_odd_palindrome_partial_solve_wit_4.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_5_pure : even_odd_palindrome_partial_solve_wit_5_pure.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_5 : even_odd_palindrome_partial_solve_wit_5.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_6_pure : even_odd_palindrome_partial_solve_wit_6_pure.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_6 : even_odd_palindrome_partial_solve_wit_6.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_7 : even_odd_palindrome_partial_solve_wit_7.
Axiom proof_of_even_odd_palindrome_partial_solve_wit_8 : even_odd_palindrome_partial_solve_wit_8.

End VC_Correct.
