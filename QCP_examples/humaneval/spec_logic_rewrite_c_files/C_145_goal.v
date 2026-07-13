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
Require Import coins_145.
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
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
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
  &&  “ (0 <= (-x_pre)) ” 
  &&  “ ((-x_pre) <= INT_MAX) ”
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

(*----- Function signed_digit_score -----*)

Definition signed_digit_score_safety_wit_1 := 
forall (x_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (INT_MIN < x_pre)) (PreH5 : (x_pre < INT_MAX)) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "msd" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition signed_digit_score_safety_wit_2 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre < INT_MAX)) (PreH3 : (0 <= t)) (PreH4 : (t <= INT_MAX)) (PreH5 : (sum = 0)) (PreH6 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |->_)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_safety_wit_3 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t >= 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |->_)
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition signed_digit_score_safety_wit_4 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t >= 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |->_)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_safety_wit_5 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (x_pre < 0)) (PreH2 : (t < 10)) (PreH3 : (INT_MIN < x_pre)) (PreH4 : (x_pre < INT_MAX)) (PreH5 : (0 <= t)) (PreH6 : (t <= INT_MAX)) (PreH7 : (sum = 0)) (PreH8 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ ((sum + (-t) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (-t) )) ”
.

Definition signed_digit_score_safety_wit_6 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (t < 10)) (PreH3 : (INT_MIN < x_pre)) (PreH4 : (x_pre < INT_MAX)) (PreH5 : (0 <= t)) (PreH6 : (t <= INT_MAX)) (PreH7 : (sum = 0)) (PreH8 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ ((sum + t ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + t )) ”
.

Definition signed_digit_score_safety_wit_7 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t < 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition signed_digit_score_safety_wit_8 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (x_pre < 0)) (PreH2 : (t < 10)) (PreH3 : (INT_MIN < x_pre)) (PreH4 : (x_pre < INT_MAX)) (PreH5 : (0 <= t)) (PreH6 : (t <= INT_MAX)) (PreH7 : (sum = 0)) (PreH8 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (t <> (INT_MIN)) ”
.

Definition signed_digit_score_safety_wit_9 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (x_pre >= 0)) (PreH5 : (t < 10)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (x_pre < INT_MAX)) (PreH8 : (0 <= t)) (PreH9 : (t <= INT_MAX)) (PreH10 : (sum = 0)) (PreH11 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_safety_wit_10 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (x_pre < 0)) (PreH5 : (t < 10)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (x_pre < INT_MAX)) (PreH8 : (0 <= t)) (PreH9 : (t <= INT_MAX)) (PreH10 : (sum = 0)) (PreH11 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_safety_wit_11 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition signed_digit_score_safety_wit_12 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition signed_digit_score_safety_wit_13 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre < INT_MAX)) (PreH3 : (10 <= t)) (PreH4 : (t <= INT_MAX)) (PreH5 : (1 <= p)) (PreH6 : (p <= t)) (PreH7 : ((INT_MIN + 10 ) <= sum)) (PreH8 : (sum <= (INT_MAX - 10 ))) (PreH9 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition signed_digit_score_safety_wit_14 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre < INT_MAX)) (PreH3 : (10 <= t)) (PreH4 : (t <= INT_MAX)) (PreH5 : (1 <= p)) (PreH6 : (p <= t)) (PreH7 : ((INT_MIN + 10 ) <= sum)) (PreH8 : (sum <= (INT_MAX - 10 ))) (PreH9 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_safety_wit_15 := 
(
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((p * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p * 10 )) ”
) \/
(
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((p * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p * 10 )) ”
).

Definition signed_digit_score_safety_wit_15_split_goal_1 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((p * 10 ) <= INT_MAX) ”
.

Definition signed_digit_score_safety_wit_15_split_goal_2 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((INT_MIN) <= (p * 10 )) ”
.

Definition signed_digit_score_safety_wit_16 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_safety_wit_17 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p > (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((t <> (INT_MIN)) \/ (p <> (-1))) ” 
  &&  “ (p <> 0) ”
.

Definition signed_digit_score_safety_wit_18 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition signed_digit_score_safety_wit_19 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition signed_digit_score_safety_wit_20 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre < INT_MAX)) (PreH3 : (0 <= t)) (PreH4 : (t <= INT_MAX)) (PreH5 : (INT_MIN <= sum)) (PreH6 : (sum <= INT_MAX)) (PreH7 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition signed_digit_score_safety_wit_21 := 
(
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((sum + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (t % ( 10 ) ) )) ”
) \/
(
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((sum + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (t % ( 10 ) ) )) ”
).

Definition signed_digit_score_safety_wit_21_split_goal_1 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((sum + (t % ( 10 ) ) ) <= INT_MAX) ”
.

Definition signed_digit_score_safety_wit_21_split_goal_2 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((INT_MIN) <= (sum + (t % ( 10 ) ) )) ”
.

Definition signed_digit_score_safety_wit_22 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition signed_digit_score_safety_wit_23 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_safety_wit_24 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (t % ( 10 ) ) ))
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition signed_digit_score_safety_wit_25 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (t % ( 10 ) ) ))
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition signed_digit_score_entail_wit_1 := 
(
forall (x_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (INT_MIN < x_pre)) (PreH5 : (x_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (first_digit_state_145 (Zabs (x_pre)) retval ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (INT_MIN < x_pre)) (PreH5 : (x_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (first_digit_state_145 (Zabs (x_pre)) retval ) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (x_pre)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (INT_MIN < x_pre)) (PreH5 : (x_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (first_digit_state_145 (Zabs (x_pre)) retval ) ”
.

Definition signed_digit_score_entail_wit_2 := 
(
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t >= 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= (t ÷ 10 )) ” 
  &&  “ ((t ÷ 10 ) <= INT_MAX) ” 
  &&  “ (sum = 0) ” 
  &&  “ (first_digit_state_145 (Zabs (x_pre)) (t ÷ 10 ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t >= 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (first_digit_state_145 (Zabs (x_pre)) (t ÷ 10 ) ) ” 
  &&  “ ((t ÷ 10 ) <= INT_MAX) ” 
  &&  “ (0 <= (t ÷ 10 )) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t >= 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (first_digit_state_145 (Zabs (x_pre)) (t ÷ 10 ) ) ”
.

Definition signed_digit_score_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t >= 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ ((t ÷ 10 ) <= INT_MAX) ”
.

Definition signed_digit_score_entail_wit_2_split_goal_3 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t >= 10)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (sum = 0)) (PreH7 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (0 <= (t ÷ 10 )) ”
.

Definition signed_digit_score_entail_wit_3_1 := 
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (10 <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= retval) ” 
  &&  “ ((INT_MIN + 10 ) <= (sum + t )) ” 
  &&  “ ((sum + t ) <= (INT_MAX - 10 )) ” 
  &&  “ (highest_power10_state_145 x_pre retval 1 (sum + t ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (highest_power10_state_145 x_pre retval 1 (sum + t ) ) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_3_1_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (highest_power10_state_145 x_pre retval 1 (sum + t ) ) ”
.

Definition signed_digit_score_entail_wit_3_2 := 
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (10 <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= retval) ” 
  &&  “ ((INT_MIN + 10 ) <= (sum + (-t) )) ” 
  &&  “ ((sum + (-t) ) <= (INT_MAX - 10 )) ” 
  &&  “ (highest_power10_state_145 x_pre retval 1 (sum + (-t) ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (highest_power10_state_145 x_pre retval 1 (sum + (-t) ) ) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_3_2_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval >= 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (highest_power10_state_145 x_pre retval 1 (sum + (-t) ) ) ”
.

Definition signed_digit_score_entail_wit_4 := 
(
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (10 <= t) ” 
  &&  “ (t <= INT_MAX) ” 
  &&  “ (1 <= (p * 10 )) ” 
  &&  “ ((p * 10 ) <= t) ” 
  &&  “ ((INT_MIN + 10 ) <= sum) ” 
  &&  “ (sum <= (INT_MAX - 10 )) ” 
  &&  “ (highest_power10_state_145 x_pre t (p * 10 ) sum ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ (highest_power10_state_145 x_pre t (p * 10 ) sum ) ” 
  &&  “ ((p * 10 ) <= t) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_4_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ (highest_power10_state_145 x_pre t (p * 10 ) sum ) ”
.

Definition signed_digit_score_entail_wit_4_split_goal_2 := 
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p <= (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ ((p * 10 ) <= t) ”
.

Definition signed_digit_score_entail_wit_5_1 := 
(
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p > (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= (t % ( p ) )) ” 
  &&  “ ((t % ( p ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (signed_digit_tail_state_145 x_pre (t % ( p ) ) sum ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p > (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre (t % ( p ) ) sum ) ” 
  &&  “ ((t % ( p ) ) <= INT_MAX) ” 
  &&  “ (0 <= (t % ( p ) )) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_5_1_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p > (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre (t % ( p ) ) sum ) ”
.

Definition signed_digit_score_entail_wit_5_1_split_goal_2 := 
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p > (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ ((t % ( p ) ) <= INT_MAX) ”
.

Definition signed_digit_score_entail_wit_5_1_split_goal_3 := 
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) (PreH1 : (p > (t ÷ 10 ))) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (10 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (1 <= p)) (PreH7 : (p <= t)) (PreH8 : ((INT_MIN + 10 ) <= sum)) (PreH9 : (sum <= (INT_MAX - 10 ))) (PreH10 : (highest_power10_state_145 x_pre t p sum )) ,
  TT && emp 
|--
  “ (0 <= (t % ( p ) )) ”
.

Definition signed_digit_score_entail_wit_5_2 := 
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + t )) ” 
  &&  “ ((sum + t ) <= INT_MAX) ” 
  &&  “ (signed_digit_tail_state_145 x_pre 0 (sum + t ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre 0 (sum + t ) ) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_5_2_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre >= 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre 0 (sum + t ) ) ”
.

Definition signed_digit_score_entail_wit_5_3 := 
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + (-t) )) ” 
  &&  “ ((sum + (-t) ) <= INT_MAX) ” 
  &&  “ (signed_digit_tail_state_145 x_pre 0 (sum + (-t) ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre 0 (sum + (-t) ) ) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_5_3_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) (PreH1 : (retval < 10)) (PreH2 : (retval = (Zabs (x_pre)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (x_pre < 0)) (PreH6 : (t < 10)) (PreH7 : (INT_MIN < x_pre)) (PreH8 : (x_pre < INT_MAX)) (PreH9 : (0 <= t)) (PreH10 : (t <= INT_MAX)) (PreH11 : (sum = 0)) (PreH12 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre 0 (sum + (-t) ) ) ”
.

Definition signed_digit_score_entail_wit_6 := 
(
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= (t ÷ 10 )) ” 
  &&  “ ((t ÷ 10 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + (t % ( 10 ) ) )) ” 
  &&  “ ((sum + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (signed_digit_tail_state_145 x_pre (t ÷ 10 ) (sum + (t % ( 10 ) ) ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre (t ÷ 10 ) (sum + (t % ( 10 ) ) ) ) ” 
  &&  “ ((sum + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + (t % ( 10 ) ) )) ” 
  &&  “ ((t ÷ 10 ) <= INT_MAX) ” 
  &&  “ (0 <= (t ÷ 10 )) ”
  &&  emp
).

Definition signed_digit_score_entail_wit_6_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (signed_digit_tail_state_145 x_pre (t ÷ 10 ) (sum + (t % ( 10 ) ) ) ) ”
.

Definition signed_digit_score_entail_wit_6_split_goal_2 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ ((sum + (t % ( 10 ) ) ) <= INT_MAX) ”
.

Definition signed_digit_score_entail_wit_6_split_goal_3 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (INT_MIN <= (sum + (t % ( 10 ) ) )) ”
.

Definition signed_digit_score_entail_wit_6_split_goal_4 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ ((t ÷ 10 ) <= INT_MAX) ”
.

Definition signed_digit_score_entail_wit_6_split_goal_5 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t > 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (0 <= (t ÷ 10 )) ”
.

Definition signed_digit_score_return_wit_1 := 
(
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t <= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (signed_digit_score_result_145 x_pre sum ) ” 
  &&  “ (INT_MIN < sum) ” 
  &&  “ (sum < INT_MAX) ”
  &&  emp
) \/
(
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t <= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (sum < INT_MAX) ” 
  &&  “ (INT_MIN < sum) ” 
  &&  “ (signed_digit_score_result_145 x_pre sum ) ”
  &&  emp
).

Definition signed_digit_score_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t <= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (sum < INT_MAX) ”
.

Definition signed_digit_score_return_wit_1_split_goal_2 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t <= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (INT_MIN < sum) ”
.

Definition signed_digit_score_return_wit_1_split_goal_3 := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (t <= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre < INT_MAX)) (PreH4 : (0 <= t)) (PreH5 : (t <= INT_MAX)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (signed_digit_tail_state_145 x_pre t sum )) ,
  TT && emp 
|--
  “ (signed_digit_score_result_145 x_pre sum ) ”
.

Definition signed_digit_score_partial_solve_wit_1_pure := 
forall (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
.

Definition signed_digit_score_partial_solve_wit_1_aux := 
forall (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ”
  &&  emp
.

Definition signed_digit_score_partial_solve_wit_1 := signed_digit_score_partial_solve_wit_1_pure -> signed_digit_score_partial_solve_wit_1_aux.

Definition signed_digit_score_partial_solve_wit_2_pure := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (t < 10)) (PreH3 : (INT_MIN < x_pre)) (PreH4 : (x_pre < INT_MAX)) (PreH5 : (0 <= t)) (PreH6 : (t <= INT_MAX)) (PreH7 : (sum = 0)) (PreH8 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
.

Definition signed_digit_score_partial_solve_wit_2_aux := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (t < 10)) (PreH3 : (INT_MIN < x_pre)) (PreH4 : (x_pre < INT_MAX)) (PreH5 : (0 <= t)) (PreH6 : (t <= INT_MAX)) (PreH7 : (sum = 0)) (PreH8 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (x_pre >= 0) ” 
  &&  “ (t < 10) ” 
  &&  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= INT_MAX) ” 
  &&  “ (sum = 0) ” 
  &&  “ (first_digit_state_145 (Zabs (x_pre)) t ) ”
  &&  emp
.

Definition signed_digit_score_partial_solve_wit_2 := signed_digit_score_partial_solve_wit_2_pure -> signed_digit_score_partial_solve_wit_2_aux.

Definition signed_digit_score_partial_solve_wit_3_pure := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (x_pre < 0)) (PreH2 : (t < 10)) (PreH3 : (INT_MIN < x_pre)) (PreH4 : (x_pre < INT_MAX)) (PreH5 : (0 <= t)) (PreH6 : (t <= INT_MAX)) (PreH7 : (sum = 0)) (PreH8 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
.

Definition signed_digit_score_partial_solve_wit_3_aux := 
forall (x_pre: Z) (sum: Z) (t: Z) (PreH1 : (x_pre < 0)) (PreH2 : (t < 10)) (PreH3 : (INT_MIN < x_pre)) (PreH4 : (x_pre < INT_MAX)) (PreH5 : (0 <= t)) (PreH6 : (t <= INT_MAX)) (PreH7 : (sum = 0)) (PreH8 : (first_digit_state_145 (Zabs (x_pre)) t )) ,
  TT && emp 
|--
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (x_pre < 0) ” 
  &&  “ (t < 10) ” 
  &&  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= INT_MAX) ” 
  &&  “ (sum = 0) ” 
  &&  “ (first_digit_state_145 (Zabs (x_pre)) t ) ”
  &&  emp
.

Definition signed_digit_score_partial_solve_wit_3 := signed_digit_score_partial_solve_wit_3_pure -> signed_digit_score_partial_solve_wit_3_aux.

(*----- Function order_by_points -----*)

Definition order_by_points_safety_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  ((( &( "m" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_by_points_safety_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_by_points_safety_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_by_points_safety_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) (m_addr_v: Z) (s_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < nums_size_pre)) (PreH11 : ((i + 1 ) = (Zlength (output_l)))) (PreH12 : (order_copy_prefix_145 (i + 1 ) input_l output_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition order_by_points_safety_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_by_points_safety_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) (m_addr_v: Z) (s_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < nums_size_pre)) (PreH11 : ((i + 1 ) = (Zlength (score_l)))) (PreH12 : (order_score_prefix_145 (i + 1 ) input_l score_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition order_by_points_safety_wit_7 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (order_score_prefix_145 i input_l score_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_by_points_safety_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (nums_size_pre = (Zlength (output_l)))) (PreH13 : (nums_size_pre = (Zlength (score_l)))) (PreH14 : (order_outer_state_145 i input_l initial_score_l output_l score_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_by_points_safety_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (j < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < nums_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= nums_size_pre)) (PreH14 : (nums_size_pre = (Zlength (output_l)))) (PreH15 : (nums_size_pre = (Zlength (score_l)))) (PreH16 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition order_by_points_safety_wit_10 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (j < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < nums_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= nums_size_pre)) (PreH14 : (nums_size_pre = (Zlength (output_l)))) (PreH15 : (nums_size_pre = (Zlength (score_l)))) (PreH16 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_by_points_safety_wit_11 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre score_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition order_by_points_safety_wit_12 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre score_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_by_points_safety_wit_13 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition order_by_points_safety_wit_14 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_by_points_safety_wit_15 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition order_by_points_safety_wit_16 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_by_points_safety_wit_17 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition order_by_points_safety_wit_18 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_by_points_safety_wit_19 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition order_by_points_safety_wit_20 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) <= (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre score_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition order_by_points_safety_wit_21 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (initial_score_l: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) (m_addr_v: Z) (s_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < nums_size_pre)) (PreH11 : (nums_size_pre = (Zlength (output_l)))) (PreH12 : (nums_size_pre = (Zlength (score_l)))) (PreH13 : (order_outer_state_145 (i + 1 ) input_l initial_score_l output_l score_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition order_by_points_entail_wit_1 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  (IntArray.undef_full retval_3 nums_size_pre )
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  EX (output_l: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (0 = (Zlength (output_l))) ” 
  &&  “ (order_copy_prefix_145 0 input_l output_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 nums_size_pre )
  **  (IntArray.undef_full retval_3 nums_size_pre )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  (IntArray.undef_full retval_3 nums_size_pre )
|--
  “ (order_copy_prefix_145 0 input_l (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  (IntArray.undef_full retval_3 nums_size_pre )
).

Definition order_by_points_entail_wit_1_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  (IntArray.undef_full retval_3 nums_size_pre )
|--
  “ (order_copy_prefix_145 0 input_l (@nil Z) ) ”
.

Definition order_by_points_entail_wit_1_split_goal_2 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  (IntArray.undef_full retval_3 nums_size_pre )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition order_by_points_entail_wit_1_split_goal_spatial := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) ,
  (IntArray.undef_full retval_3 nums_size_pre )
|--
  (IntArray.undef_full retval_3 nums_size_pre )
.

Definition order_by_points_entail_wit_2 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l_2)))) (PreH13 : (order_copy_prefix_145 i input_l output_l_2 )) ,
  (IntArray.seg data 0 (i + 1 ) (app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.undef_full score nums_size_pre )
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (output_l))) ” 
  &&  “ (order_copy_prefix_145 (i + 1 ) input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l_2)))) (PreH13 : (order_copy_prefix_145 i input_l output_l_2 )) ,
  (IntArray.undef_full score nums_size_pre )
|--
  “ (order_copy_prefix_145 (i + 1 ) input_l (app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) ) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z)))))))) ”
  &&  (IntArray.undef_full score nums_size_pre )
).

Definition order_by_points_entail_wit_2_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l_2)))) (PreH13 : (order_copy_prefix_145 i input_l output_l_2 )) ,
  (IntArray.undef_full score nums_size_pre )
|--
  “ (order_copy_prefix_145 (i + 1 ) input_l (app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) ) ”
.

Definition order_by_points_entail_wit_2_split_goal_2 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l_2)))) (PreH13 : (order_copy_prefix_145 i input_l output_l_2 )) ,
  (IntArray.undef_full score nums_size_pre )
|--
  “ ((i + 1 ) = (Zlength ((app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z)))))))) ”
.

Definition order_by_points_entail_wit_2_split_goal_spatial := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l_2)))) (PreH13 : (order_copy_prefix_145 i input_l output_l_2 )) ,
  (IntArray.undef_full score nums_size_pre )
|--
  (IntArray.undef_full score nums_size_pre )
.

Definition order_by_points_entail_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < nums_size_pre)) (PreH11 : ((i + 1 ) = (Zlength (output_l_2)))) (PreH12 : (order_copy_prefix_145 (i + 1 ) input_l output_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l_2 )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nums_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (output_l))) ” 
  &&  “ (order_copy_prefix_145 (i + 1 ) input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
.

Definition order_by_points_entail_wit_4 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (0 = (Zlength (score_l))) ” 
  &&  “ (order_score_prefix_145 0 input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 0 score_l )
  **  (IntArray.undef_seg score 0 nums_size_pre )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  (IntArray.seg data 0 i output_l )
|--
  “ (order_score_prefix_145 0 input_l (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  (IntArray.full data nums_size_pre input_l )
).

Definition order_by_points_entail_wit_4_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  (IntArray.seg data 0 i output_l )
|--
  “ (order_score_prefix_145 0 input_l (@nil Z) ) ”
.

Definition order_by_points_entail_wit_4_split_goal_2 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  (IntArray.seg data 0 i output_l )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition order_by_points_entail_wit_4_split_goal_spatial := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  (IntArray.seg data 0 i output_l )
|--
  (IntArray.full data nums_size_pre input_l )
.

Definition order_by_points_entail_wit_5 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (retval: Z) (PreH1 : (signed_digit_score_result_145 (Znth i input_l 0) retval )) (PreH2 : (INT_MIN < retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i < nums_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (score <> 0)) (PreH8 : (0 <= nums_size_pre)) (PreH9 : (nums_size_pre < INT_MAX)) (PreH10 : (nums_size_pre = (Zlength (input_l)))) (PreH11 : (problem_145_pre_z input_l )) (PreH12 : (order_by_points_safe_145 input_l )) (PreH13 : (0 <= i)) (PreH14 : (i <= nums_size_pre)) (PreH15 : (i = (Zlength (score_l_2)))) (PreH16 : (order_score_prefix_145 i input_l score_l_2 )) ,
  (IntArray.seg score 0 (i + 1 ) (app (score_l_2) ((cons (retval) ((@nil Z))))) )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full data nums_size_pre input_l )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (score_l))) ” 
  &&  “ (order_score_prefix_145 (i + 1 ) input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (retval: Z) (PreH1 : (signed_digit_score_result_145 (Znth i input_l 0) retval )) (PreH2 : (INT_MIN < retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i < nums_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (score <> 0)) (PreH8 : (0 <= nums_size_pre)) (PreH9 : (nums_size_pre < INT_MAX)) (PreH10 : (nums_size_pre = (Zlength (input_l)))) (PreH11 : (problem_145_pre_z input_l )) (PreH12 : (order_by_points_safe_145 input_l )) (PreH13 : (0 <= i)) (PreH14 : (i <= nums_size_pre)) (PreH15 : (i = (Zlength (score_l_2)))) (PreH16 : (order_score_prefix_145 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (order_score_prefix_145 (i + 1 ) input_l (app (score_l_2) ((cons (retval) ((@nil Z))))) ) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (score_l_2) ((cons (retval) ((@nil Z)))))))) ”
  &&  emp
).

Definition order_by_points_entail_wit_5_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (retval: Z) (PreH1 : (signed_digit_score_result_145 (Znth i input_l 0) retval )) (PreH2 : (INT_MIN < retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i < nums_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (score <> 0)) (PreH8 : (0 <= nums_size_pre)) (PreH9 : (nums_size_pre < INT_MAX)) (PreH10 : (nums_size_pre = (Zlength (input_l)))) (PreH11 : (problem_145_pre_z input_l )) (PreH12 : (order_by_points_safe_145 input_l )) (PreH13 : (0 <= i)) (PreH14 : (i <= nums_size_pre)) (PreH15 : (i = (Zlength (score_l_2)))) (PreH16 : (order_score_prefix_145 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (order_score_prefix_145 (i + 1 ) input_l (app (score_l_2) ((cons (retval) ((@nil Z))))) ) ”
.

Definition order_by_points_entail_wit_5_split_goal_2 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (retval: Z) (PreH1 : (signed_digit_score_result_145 (Znth i input_l 0) retval )) (PreH2 : (INT_MIN < retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i < nums_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (score <> 0)) (PreH8 : (0 <= nums_size_pre)) (PreH9 : (nums_size_pre < INT_MAX)) (PreH10 : (nums_size_pre = (Zlength (input_l)))) (PreH11 : (problem_145_pre_z input_l )) (PreH12 : (order_by_points_safe_145 input_l )) (PreH13 : (0 <= i)) (PreH14 : (i <= nums_size_pre)) (PreH15 : (i = (Zlength (score_l_2)))) (PreH16 : (order_score_prefix_145 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ ((i + 1 ) = (Zlength ((app (score_l_2) ((cons (retval) ((@nil Z)))))))) ”
.

Definition order_by_points_entail_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < nums_size_pre)) (PreH11 : ((i + 1 ) = (Zlength (score_l_2)))) (PreH12 : (order_score_prefix_145 (i + 1 ) input_l score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 (i + 1 ) score_l_2 )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nums_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (score_l))) ” 
  &&  “ (order_score_prefix_145 (i + 1 ) input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
.

Definition order_by_points_entail_wit_7 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (order_score_prefix_145 i input_l score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l_2 )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  EX (initial_score_l: (@list Z))  (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_outer_state_145 0 input_l initial_score_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (order_score_prefix_145 i input_l score_l_2 )) ,
  (IntArray.seg score 0 i score_l_2 )
|--
  EX (initial_score_l: (@list Z))  (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_outer_state_145 0 input_l initial_score_l input_l score_l ) ”
  &&  (IntArray.full score nums_size_pre score_l )
).

Definition order_by_points_entail_wit_8 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (nums_size_pre = (Zlength (output_l_2)))) (PreH13 : (nums_size_pre = (Zlength (score_l_2)))) (PreH14 : (order_outer_state_145 i input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (initial_score_l: (@list Z))  (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i 1 input_l initial_score_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (nums_size_pre = (Zlength (output_l_2)))) (PreH13 : (nums_size_pre = (Zlength (score_l_2)))) (PreH14 : (order_outer_state_145 i input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  TT && emp 
|--
  EX (initial_score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l_2))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l_2))) ” 
  &&  “ (order_inner_state_145 i 1 input_l initial_score_l output_l_2 score_l_2 ) ”
  &&  emp
).

Definition order_by_points_entail_wit_9 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (j >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < nums_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= nums_size_pre)) (PreH14 : (nums_size_pre = (Zlength (output_l_2)))) (PreH15 : (nums_size_pre = (Zlength (score_l_2)))) (PreH16 : (order_inner_state_145 i j input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (initial_score_l: (@list Z))  (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_outer_state_145 (i + 1 ) input_l initial_score_l output_l score_l ) ”
  &&  ((( &( "j" ) )) # Int  |-> nums_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (j >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < nums_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= nums_size_pre)) (PreH14 : (nums_size_pre = (Zlength (output_l_2)))) (PreH15 : (nums_size_pre = (Zlength (score_l_2)))) (PreH16 : (order_inner_state_145 i j input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  TT && emp 
|--
  EX (initial_score_l: (@list Z)) ,
  “ (j = nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l_2))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l_2))) ” 
  &&  “ (order_outer_state_145 (i + 1 ) input_l initial_score_l output_l_2 score_l_2 ) ”
  &&  emp
).

Definition order_by_points_entail_wit_10_1 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l_2 0) > (Znth j score_l_2 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l_2)))) (PreH16 : (nums_size_pre = (Zlength (score_l_2)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  (IntArray.full data nums_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  EX (initial_score_l: (@list Z))  (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i (j + 1 ) input_l initial_score_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l_2 0) > (Znth j score_l_2 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l_2)))) (PreH16 : (nums_size_pre = (Zlength (score_l_2)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  TT && emp 
|--
  EX (initial_score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2))))))) ” 
  &&  “ (nums_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2))))))) ” 
  &&  “ (order_inner_state_145 i (j + 1 ) input_l initial_score_l (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) ) ”
  &&  emp
).

Definition order_by_points_entail_wit_10_2 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l_2 0) <= (Znth j score_l_2 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l_2)))) (PreH16 : (nums_size_pre = (Zlength (score_l_2)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  (IntArray.full score nums_size_pre score_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
|--
  EX (initial_score_l: (@list Z))  (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i (j + 1 ) input_l initial_score_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (initial_score_l_2: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l_2 0) <= (Znth j score_l_2 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l_2)))) (PreH16 : (nums_size_pre = (Zlength (score_l_2)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  TT && emp 
|--
  EX (initial_score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l_2))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l_2))) ” 
  &&  “ (order_inner_state_145 i (j + 1 ) input_l initial_score_l output_l_2 score_l_2 ) ”
  &&  emp
).

Definition order_by_points_entail_wit_11 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (score_l_2: (@list Z)) (initial_score_l_2: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (problem_145_pre_z input_l )) (PreH8 : (order_by_points_safe_145 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < nums_size_pre)) (PreH11 : (nums_size_pre = (Zlength (output_l_2)))) (PreH12 : (nums_size_pre = (Zlength (score_l_2)))) (PreH13 : (order_outer_state_145 (i + 1 ) input_l initial_score_l_2 output_l_2 score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (initial_score_l: (@list Z))  (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_outer_state_145 (i + 1 ) input_l initial_score_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_entail_wit_12 := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (nums_size_pre = (Zlength (output_l_2)))) (PreH13 : (nums_size_pre = (Zlength (score_l_2)))) (PreH14 : (order_outer_state_145 i input_l initial_score_l output_l_2 score_l_2 )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (problem_145_spec_z input_l output_l ) ”
  &&  ((( &( "i" ) )) # Int  |-> nums_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
) \/
(
forall (nums_size_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (nums_size_pre = (Zlength (output_l_2)))) (PreH13 : (nums_size_pre = (Zlength (score_l_2)))) (PreH14 : (order_outer_state_145 i input_l initial_score_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (problem_145_spec_z input_l output_l_2 ) ”
  &&  emp
).

Definition order_by_points_entail_wit_12_split_goal_1 := 
forall (nums_size_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i >= nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (nums_size_pre = (Zlength (output_l_2)))) (PreH13 : (nums_size_pre = (Zlength (score_l_2)))) (PreH14 : (order_outer_state_145 i input_l initial_score_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (problem_145_spec_z input_l output_l_2 ) ”
.

Definition order_by_points_return_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (score_l: (@list Z)) (out: Z) (data_2: Z) (score: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (nums_size_pre = (Zlength (output_l_2)))) (PreH8 : (nums_size_pre = (Zlength (score_l)))) (PreH9 : (problem_145_spec_z input_l output_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data_2 nums_size_pre output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = nums_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (problem_145_spec_z input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data output_size output_l )
.

Definition order_by_points_partial_solve_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= nums_size_pre)) (PreH2 : (nums_size_pre < INT_MAX)) (PreH3 : (nums_size_pre = (Zlength (input_l)))) (PreH4 : (problem_145_pre_z input_l )) (PreH5 : (order_by_points_safe_145 input_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_2_pure := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_145_pre_z input_l )) (PreH6 : (order_by_points_safe_145 input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (nums_size_pre >= 0) ” 
  &&  “ (nums_size_pre < INT_MAX) ”
.

Definition order_by_points_partial_solve_wit_2_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= nums_size_pre)) (PreH3 : (nums_size_pre < INT_MAX)) (PreH4 : (nums_size_pre = (Zlength (input_l)))) (PreH5 : (problem_145_pre_z input_l )) (PreH6 : (order_by_points_safe_145 input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (nums_size_pre >= 0) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_2 := order_by_points_partial_solve_wit_2_pure -> order_by_points_partial_solve_wit_2_aux.

Definition order_by_points_partial_solve_wit_3_pure := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_145_pre_z input_l )) (PreH7 : (order_by_points_safe_145 input_l )) ,
  ((( &( "score" ) )) # Ptr  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (nums_size_pre >= 0) ” 
  &&  “ (nums_size_pre < INT_MAX) ”
.

Definition order_by_points_partial_solve_wit_3_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= nums_size_pre)) (PreH4 : (nums_size_pre < INT_MAX)) (PreH5 : (nums_size_pre = (Zlength (input_l)))) (PreH6 : (problem_145_pre_z input_l )) (PreH7 : (order_by_points_safe_145 input_l )) ,
  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ (nums_size_pre >= 0) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ”
  &&  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_3 := order_by_points_partial_solve_wit_3_pure -> order_by_points_partial_solve_wit_3_aux.

Definition order_by_points_partial_solve_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
|--
  “ (i < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nums_size_pre) ” 
  &&  “ (i = (Zlength (output_l))) ” 
  &&  “ (order_copy_prefix_145 i input_l output_l ) ”
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
.

Definition order_by_points_partial_solve_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (output_l)))) (PreH13 : (order_copy_prefix_145 i input_l output_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.undef_full score nums_size_pre )
|--
  “ (i < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nums_size_pre) ” 
  &&  “ (i = (Zlength (output_l))) ” 
  &&  “ (order_copy_prefix_145 i input_l output_l ) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_full score nums_size_pre )
.

Definition order_by_points_partial_solve_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (order_score_prefix_145 i input_l score_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ (i < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nums_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (order_score_prefix_145 i input_l score_l ) ”
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
.

Definition order_by_points_partial_solve_wit_7_pure := 
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (order_score_prefix_145 i input_l score_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ ((Znth i input_l 0) < INT_MAX) ” 
  &&  “ (INT_MIN < (Znth i input_l 0)) ”
) \/
(
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (s_addr_v <= INT_MAX)) (PreH2 : (m_addr_v <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (nums_size_pre <= INT_MAX)) (PreH5 : (s_addr_v >= INT_MIN)) (PreH6 : (m_addr_v >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (nums_size_pre >= INT_MIN)) (PreH9 : (i < nums_size_pre)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (score <> 0)) (PreH13 : (0 <= nums_size_pre)) (PreH14 : (nums_size_pre < INT_MAX)) (PreH15 : (nums_size_pre = (Zlength (input_l)))) (PreH16 : (problem_145_pre_z input_l )) (PreH17 : (order_by_points_safe_145 input_l )) (PreH18 : (0 <= i)) (PreH19 : (i <= nums_size_pre)) (PreH20 : (i = (Zlength (score_l)))) (PreH21 : (order_score_prefix_145 i input_l score_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ (INT_MIN < (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) < INT_MAX) ”
).

Definition order_by_points_partial_solve_wit_7_pure_split_goal_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (s_addr_v <= INT_MAX)) (PreH2 : (m_addr_v <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (nums_size_pre <= INT_MAX)) (PreH5 : (s_addr_v >= INT_MIN)) (PreH6 : (m_addr_v >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (nums_size_pre >= INT_MIN)) (PreH9 : (i < nums_size_pre)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (score <> 0)) (PreH13 : (0 <= nums_size_pre)) (PreH14 : (nums_size_pre < INT_MAX)) (PreH15 : (nums_size_pre = (Zlength (input_l)))) (PreH16 : (problem_145_pre_z input_l )) (PreH17 : (order_by_points_safe_145 input_l )) (PreH18 : (0 <= i)) (PreH19 : (i <= nums_size_pre)) (PreH20 : (i = (Zlength (score_l)))) (PreH21 : (order_score_prefix_145 i input_l score_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ (INT_MIN < (Znth i input_l 0)) ”
.

Definition order_by_points_partial_solve_wit_7_pure_split_goal_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (s_addr_v: Z) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (s_addr_v <= INT_MAX)) (PreH2 : (m_addr_v <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (nums_size_pre <= INT_MAX)) (PreH5 : (s_addr_v >= INT_MIN)) (PreH6 : (m_addr_v >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (nums_size_pre >= INT_MIN)) (PreH9 : (i < nums_size_pre)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (score <> 0)) (PreH13 : (0 <= nums_size_pre)) (PreH14 : (nums_size_pre < INT_MAX)) (PreH15 : (nums_size_pre = (Zlength (input_l)))) (PreH16 : (problem_145_pre_z input_l )) (PreH17 : (order_by_points_safe_145 input_l )) (PreH18 : (0 <= i)) (PreH19 : (i <= nums_size_pre)) (PreH20 : (i = (Zlength (score_l)))) (PreH21 : (order_score_prefix_145 i input_l score_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ ((Znth i input_l 0) < INT_MAX) ”
.

Definition order_by_points_partial_solve_wit_7_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (i < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= nums_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (order_score_prefix_145 i input_l score_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ ((Znth i input_l 0) < INT_MAX) ” 
  &&  “ (INT_MIN < (Znth i input_l 0)) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nums_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (order_score_prefix_145 i input_l score_l ) ”
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
.

Definition order_by_points_partial_solve_wit_7 := order_by_points_partial_solve_wit_7_pure -> order_by_points_partial_solve_wit_7_aux.

Definition order_by_points_partial_solve_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (retval: Z) (PreH1 : (signed_digit_score_result_145 (Znth i input_l 0) retval )) (PreH2 : (INT_MIN < retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i < nums_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (score <> 0)) (PreH8 : (0 <= nums_size_pre)) (PreH9 : (nums_size_pre < INT_MAX)) (PreH10 : (nums_size_pre = (Zlength (input_l)))) (PreH11 : (problem_145_pre_z input_l )) (PreH12 : (order_by_points_safe_145 input_l )) (PreH13 : (0 <= i)) (PreH14 : (i <= nums_size_pre)) (PreH15 : (i = (Zlength (score_l)))) (PreH16 : (order_score_prefix_145 i input_l score_l )) ,
  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  “ (signed_digit_score_result_145 (Znth i input_l 0) retval ) ” 
  &&  “ (INT_MIN < retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nums_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (order_score_prefix_145 i input_l score_l ) ”
  &&  (((score + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full data nums_size_pre input_l )
  **  (IntArray.seg score 0 i score_l )
.

Definition order_by_points_partial_solve_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (j < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < nums_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= nums_size_pre)) (PreH14 : (nums_size_pre = (Zlength (output_l)))) (PreH15 : (nums_size_pre = (Zlength (score_l)))) (PreH16 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((score + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i score (j - 1 ) 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_10 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : (j < nums_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (score <> 0)) (PreH5 : (0 <= nums_size_pre)) (PreH6 : (nums_size_pre < INT_MAX)) (PreH7 : (nums_size_pre = (Zlength (input_l)))) (PreH8 : (problem_145_pre_z input_l )) (PreH9 : (order_by_points_safe_145 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < nums_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= nums_size_pre)) (PreH14 : (nums_size_pre = (Zlength (output_l)))) (PreH15 : (nums_size_pre = (Zlength (score_l)))) (PreH16 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((score + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i score j 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_11 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((score + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i score j 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_12 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((score + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i score (j - 1 ) 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_13 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((score + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i score j 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_14 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((score + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i score (j - 1 ) 0 nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_15 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.missing_i data j 0 nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_16 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) output_l 0))
  **  (IntArray.missing_i data (j - 1 ) 0 nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_17 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((data + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data j 0 nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_18 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (initial_score_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) (PreH1 : ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0))) (PreH2 : (j < nums_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (score <> 0)) (PreH6 : (0 <= nums_size_pre)) (PreH7 : (nums_size_pre < INT_MAX)) (PreH8 : (nums_size_pre = (Zlength (input_l)))) (PreH9 : (problem_145_pre_z input_l )) (PreH10 : (order_by_points_safe_145 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < nums_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= nums_size_pre)) (PreH15 : (nums_size_pre = (Zlength (output_l)))) (PreH16 : (nums_size_pre = (Zlength (score_l)))) (PreH17 : (order_inner_state_145 i j input_l initial_score_l output_l score_l )) ,
  (IntArray.full data nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  “ ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) ” 
  &&  “ (j < nums_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_145_pre_z input_l ) ” 
  &&  “ (order_by_points_safe_145 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nums_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= nums_size_pre) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (order_inner_state_145 i j input_l initial_score_l output_l score_l ) ”
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data (j - 1 ) 0 nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_19_pure := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (score: Z) (m_addr_v: Z) (s_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (nums_size_pre = (Zlength (output_l)))) (PreH8 : (nums_size_pre = (Zlength (score_l)))) (PreH9 : (problem_145_spec_z input_l output_l )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> nums_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((( &( "s" ) )) # Int  |-> s_addr_v)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ”
.

Definition order_by_points_partial_solve_wit_19_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (score: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (score <> 0)) (PreH4 : (0 <= nums_size_pre)) (PreH5 : (nums_size_pre < INT_MAX)) (PreH6 : (nums_size_pre = (Zlength (input_l)))) (PreH7 : (nums_size_pre = (Zlength (output_l)))) (PreH8 : (nums_size_pre = (Zlength (score_l)))) (PreH9 : (problem_145_spec_z input_l output_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (score <> 0) ” 
  &&  “ (0 <= nums_size_pre) ” 
  &&  “ (nums_size_pre < INT_MAX) ” 
  &&  “ (nums_size_pre = (Zlength (input_l))) ” 
  &&  “ (nums_size_pre = (Zlength (output_l))) ” 
  &&  “ (nums_size_pre = (Zlength (score_l))) ” 
  &&  “ (problem_145_spec_z input_l output_l ) ”
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_19 := order_by_points_partial_solve_wit_19_pure -> order_by_points_partial_solve_wit_19_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_signed_digit_score_safety_wit_1 : signed_digit_score_safety_wit_1.
Axiom proof_of_signed_digit_score_safety_wit_2 : signed_digit_score_safety_wit_2.
Axiom proof_of_signed_digit_score_safety_wit_3 : signed_digit_score_safety_wit_3.
Axiom proof_of_signed_digit_score_safety_wit_4 : signed_digit_score_safety_wit_4.
Axiom proof_of_signed_digit_score_safety_wit_5 : signed_digit_score_safety_wit_5.
Axiom proof_of_signed_digit_score_safety_wit_6 : signed_digit_score_safety_wit_6.
Axiom proof_of_signed_digit_score_safety_wit_7 : signed_digit_score_safety_wit_7.
Axiom proof_of_signed_digit_score_safety_wit_8 : signed_digit_score_safety_wit_8.
Axiom proof_of_signed_digit_score_safety_wit_9 : signed_digit_score_safety_wit_9.
Axiom proof_of_signed_digit_score_safety_wit_10 : signed_digit_score_safety_wit_10.
Axiom proof_of_signed_digit_score_safety_wit_11 : signed_digit_score_safety_wit_11.
Axiom proof_of_signed_digit_score_safety_wit_12 : signed_digit_score_safety_wit_12.
Axiom proof_of_signed_digit_score_safety_wit_13 : signed_digit_score_safety_wit_13.
Axiom proof_of_signed_digit_score_safety_wit_14 : signed_digit_score_safety_wit_14.
Axiom proof_of_signed_digit_score_safety_wit_15 : signed_digit_score_safety_wit_15.
Axiom proof_of_signed_digit_score_safety_wit_16 : signed_digit_score_safety_wit_16.
Axiom proof_of_signed_digit_score_safety_wit_17 : signed_digit_score_safety_wit_17.
Axiom proof_of_signed_digit_score_safety_wit_18 : signed_digit_score_safety_wit_18.
Axiom proof_of_signed_digit_score_safety_wit_19 : signed_digit_score_safety_wit_19.
Axiom proof_of_signed_digit_score_safety_wit_20 : signed_digit_score_safety_wit_20.
Axiom proof_of_signed_digit_score_safety_wit_21 : signed_digit_score_safety_wit_21.
Axiom proof_of_signed_digit_score_safety_wit_22 : signed_digit_score_safety_wit_22.
Axiom proof_of_signed_digit_score_safety_wit_23 : signed_digit_score_safety_wit_23.
Axiom proof_of_signed_digit_score_safety_wit_24 : signed_digit_score_safety_wit_24.
Axiom proof_of_signed_digit_score_safety_wit_25 : signed_digit_score_safety_wit_25.
Axiom proof_of_signed_digit_score_entail_wit_1 : signed_digit_score_entail_wit_1.
Axiom proof_of_signed_digit_score_entail_wit_2 : signed_digit_score_entail_wit_2.
Axiom proof_of_signed_digit_score_entail_wit_3_1 : signed_digit_score_entail_wit_3_1.
Axiom proof_of_signed_digit_score_entail_wit_3_2 : signed_digit_score_entail_wit_3_2.
Axiom proof_of_signed_digit_score_entail_wit_4 : signed_digit_score_entail_wit_4.
Axiom proof_of_signed_digit_score_entail_wit_5_1 : signed_digit_score_entail_wit_5_1.
Axiom proof_of_signed_digit_score_entail_wit_5_2 : signed_digit_score_entail_wit_5_2.
Axiom proof_of_signed_digit_score_entail_wit_5_3 : signed_digit_score_entail_wit_5_3.
Axiom proof_of_signed_digit_score_entail_wit_6 : signed_digit_score_entail_wit_6.
Axiom proof_of_signed_digit_score_return_wit_1 : signed_digit_score_return_wit_1.
Axiom proof_of_signed_digit_score_partial_solve_wit_1_pure : signed_digit_score_partial_solve_wit_1_pure.
Axiom proof_of_signed_digit_score_partial_solve_wit_1 : signed_digit_score_partial_solve_wit_1.
Axiom proof_of_signed_digit_score_partial_solve_wit_2_pure : signed_digit_score_partial_solve_wit_2_pure.
Axiom proof_of_signed_digit_score_partial_solve_wit_2 : signed_digit_score_partial_solve_wit_2.
Axiom proof_of_signed_digit_score_partial_solve_wit_3_pure : signed_digit_score_partial_solve_wit_3_pure.
Axiom proof_of_signed_digit_score_partial_solve_wit_3 : signed_digit_score_partial_solve_wit_3.
Axiom proof_of_order_by_points_safety_wit_1 : order_by_points_safety_wit_1.
Axiom proof_of_order_by_points_safety_wit_2 : order_by_points_safety_wit_2.
Axiom proof_of_order_by_points_safety_wit_3 : order_by_points_safety_wit_3.
Axiom proof_of_order_by_points_safety_wit_4 : order_by_points_safety_wit_4.
Axiom proof_of_order_by_points_safety_wit_5 : order_by_points_safety_wit_5.
Axiom proof_of_order_by_points_safety_wit_6 : order_by_points_safety_wit_6.
Axiom proof_of_order_by_points_safety_wit_7 : order_by_points_safety_wit_7.
Axiom proof_of_order_by_points_safety_wit_8 : order_by_points_safety_wit_8.
Axiom proof_of_order_by_points_safety_wit_9 : order_by_points_safety_wit_9.
Axiom proof_of_order_by_points_safety_wit_10 : order_by_points_safety_wit_10.
Axiom proof_of_order_by_points_safety_wit_11 : order_by_points_safety_wit_11.
Axiom proof_of_order_by_points_safety_wit_12 : order_by_points_safety_wit_12.
Axiom proof_of_order_by_points_safety_wit_13 : order_by_points_safety_wit_13.
Axiom proof_of_order_by_points_safety_wit_14 : order_by_points_safety_wit_14.
Axiom proof_of_order_by_points_safety_wit_15 : order_by_points_safety_wit_15.
Axiom proof_of_order_by_points_safety_wit_16 : order_by_points_safety_wit_16.
Axiom proof_of_order_by_points_safety_wit_17 : order_by_points_safety_wit_17.
Axiom proof_of_order_by_points_safety_wit_18 : order_by_points_safety_wit_18.
Axiom proof_of_order_by_points_safety_wit_19 : order_by_points_safety_wit_19.
Axiom proof_of_order_by_points_safety_wit_20 : order_by_points_safety_wit_20.
Axiom proof_of_order_by_points_safety_wit_21 : order_by_points_safety_wit_21.
Axiom proof_of_order_by_points_entail_wit_1 : order_by_points_entail_wit_1.
Axiom proof_of_order_by_points_entail_wit_2 : order_by_points_entail_wit_2.
Axiom proof_of_order_by_points_entail_wit_3 : order_by_points_entail_wit_3.
Axiom proof_of_order_by_points_entail_wit_4 : order_by_points_entail_wit_4.
Axiom proof_of_order_by_points_entail_wit_5 : order_by_points_entail_wit_5.
Axiom proof_of_order_by_points_entail_wit_6 : order_by_points_entail_wit_6.
Axiom proof_of_order_by_points_entail_wit_7 : order_by_points_entail_wit_7.
Axiom proof_of_order_by_points_entail_wit_8 : order_by_points_entail_wit_8.
Axiom proof_of_order_by_points_entail_wit_9 : order_by_points_entail_wit_9.
Axiom proof_of_order_by_points_entail_wit_10_1 : order_by_points_entail_wit_10_1.
Axiom proof_of_order_by_points_entail_wit_10_2 : order_by_points_entail_wit_10_2.
Axiom proof_of_order_by_points_entail_wit_11 : order_by_points_entail_wit_11.
Axiom proof_of_order_by_points_entail_wit_12 : order_by_points_entail_wit_12.
Axiom proof_of_order_by_points_return_wit_1 : order_by_points_return_wit_1.
Axiom proof_of_order_by_points_partial_solve_wit_1 : order_by_points_partial_solve_wit_1.
Axiom proof_of_order_by_points_partial_solve_wit_2_pure : order_by_points_partial_solve_wit_2_pure.
Axiom proof_of_order_by_points_partial_solve_wit_2 : order_by_points_partial_solve_wit_2.
Axiom proof_of_order_by_points_partial_solve_wit_3_pure : order_by_points_partial_solve_wit_3_pure.
Axiom proof_of_order_by_points_partial_solve_wit_3 : order_by_points_partial_solve_wit_3.
Axiom proof_of_order_by_points_partial_solve_wit_4 : order_by_points_partial_solve_wit_4.
Axiom proof_of_order_by_points_partial_solve_wit_5 : order_by_points_partial_solve_wit_5.
Axiom proof_of_order_by_points_partial_solve_wit_6 : order_by_points_partial_solve_wit_6.
Axiom proof_of_order_by_points_partial_solve_wit_7_pure : order_by_points_partial_solve_wit_7_pure.
Axiom proof_of_order_by_points_partial_solve_wit_7 : order_by_points_partial_solve_wit_7.
Axiom proof_of_order_by_points_partial_solve_wit_8 : order_by_points_partial_solve_wit_8.
Axiom proof_of_order_by_points_partial_solve_wit_9 : order_by_points_partial_solve_wit_9.
Axiom proof_of_order_by_points_partial_solve_wit_10 : order_by_points_partial_solve_wit_10.
Axiom proof_of_order_by_points_partial_solve_wit_11 : order_by_points_partial_solve_wit_11.
Axiom proof_of_order_by_points_partial_solve_wit_12 : order_by_points_partial_solve_wit_12.
Axiom proof_of_order_by_points_partial_solve_wit_13 : order_by_points_partial_solve_wit_13.
Axiom proof_of_order_by_points_partial_solve_wit_14 : order_by_points_partial_solve_wit_14.
Axiom proof_of_order_by_points_partial_solve_wit_15 : order_by_points_partial_solve_wit_15.
Axiom proof_of_order_by_points_partial_solve_wit_16 : order_by_points_partial_solve_wit_16.
Axiom proof_of_order_by_points_partial_solve_wit_17 : order_by_points_partial_solve_wit_17.
Axiom proof_of_order_by_points_partial_solve_wit_18 : order_by_points_partial_solve_wit_18.
Axiom proof_of_order_by_points_partial_solve_wit_19_pure : order_by_points_partial_solve_wit_19_pure.
Axiom proof_of_order_by_points_partial_solve_wit_19 : order_by_points_partial_solve_wit_19.

End VC_Correct.
