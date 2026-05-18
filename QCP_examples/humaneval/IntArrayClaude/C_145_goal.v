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
Require Import coins_145.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function abs -----*)

Definition abs_safety_wit_1 := 
forall (x_pre: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition abs_safety_wit_2 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (x_pre <> (INT_MIN)) |]
.

Definition abs_return_wit_1 := 
forall (x_pre: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| (x_pre = (Zabs (x_pre))) |]
  &&  emp
.

Definition abs_return_wit_2 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((-x_pre) = (Zabs (x_pre))) |]
  &&  emp
.

(*----- Function signed_digit_score -----*)

Definition signed_digit_score_safety_wit_1 := 
forall (x_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |]
  &&  ((( &( "msd" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition signed_digit_score_safety_wit_2 := 
forall (x_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "msd" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition signed_digit_score_safety_wit_3 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_safety_wit_4 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (t >= 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| ((t <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition signed_digit_score_safety_wit_5 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (t >= 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_safety_wit_6 := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| ((sum + (-t) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (-t) )) |]
.

Definition signed_digit_score_safety_wit_7 := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| ((sum + t ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + t )) |]
.

Definition signed_digit_score_safety_wit_8 := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition signed_digit_score_safety_wit_9 := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (t <> (INT_MIN)) |]
.

Definition signed_digit_score_safety_wit_10 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_safety_wit_11 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_safety_wit_12 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval >= 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition signed_digit_score_safety_wit_13 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval >= 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition signed_digit_score_safety_wit_14 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= p) |] 
  &&  [| (p <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t p sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| ((p * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p * 10 )) |]
.

Definition signed_digit_score_safety_wit_15 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= p) |] 
  &&  [| (p <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t p sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_safety_wit_16 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) ,
  [| ((p * 10 ) <= t) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= p) |] 
  &&  [| (p <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t p sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| ((p * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p * 10 )) |]
.

Definition signed_digit_score_safety_wit_17 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) ,
  [| ((p * 10 ) <= t) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= p) |] 
  &&  [| (p <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t p sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_safety_wit_18 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (p: Z) (t: Z) ,
  [| ((p * 10 ) > t) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= p) |] 
  &&  [| (p <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t p sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| ((t <> (INT_MIN)) \/ (p <> (-1))) |] 
  &&  [| (p <> 0) |]
.

Definition signed_digit_score_safety_wit_19 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval < 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition signed_digit_score_safety_wit_20 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval < 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition signed_digit_score_safety_wit_21 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition signed_digit_score_safety_wit_22 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (t > 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| ((sum + (t % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (t % ( 10 ) ) )) |]
.

Definition signed_digit_score_safety_wit_23 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (t > 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| ((t <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition signed_digit_score_safety_wit_24 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (t > 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_safety_wit_25 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (t > 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (t % ( 10 ) ) ))
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| ((t <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition signed_digit_score_safety_wit_26 := 
forall (x_pre: Z) (msd_addr_v: Z) (sum: Z) (t: Z) ,
  [| (t > 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (t % ( 10 ) ) ))
  **  ((( &( "msd" ) )) # Int  |-> msd_addr_v)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition signed_digit_score_entail_wit_1 := 
forall (x_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < 100000000) |] 
  &&  [| (0 = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) retval ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_2 := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (t >= 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= (t ÷ 10 )) |] 
  &&  [| ((t ÷ 10 ) < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) (t ÷ 10 ) ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_3_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval >= 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= retval) |] 
  &&  [| (retval < 100000000) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= retval) |] 
  &&  [| ((INT_MIN + 10 ) <= (sum + t )) |] 
  &&  [| ((sum + t ) <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre retval 1 (sum + t ) ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_3_2 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval >= 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= retval) |] 
  &&  [| (retval < 100000000) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= retval) |] 
  &&  [| ((INT_MIN + 10 ) <= (sum + (-t) )) |] 
  &&  [| ((sum + (-t) ) <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre retval 1 (sum + (-t) ) ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_4 := 
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) ,
  [| ((p * 10 ) <= t) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= p) |] 
  &&  [| (p <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t p sum ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= (p * 10 )) |] 
  &&  [| ((p * 10 ) <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t (p * 10 ) sum ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_5_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval < 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < 100000000) |] 
  &&  [| ((-100) <= (sum + t )) |] 
  &&  [| ((sum + t ) <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre 0 (sum + t ) ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_5_2 := 
forall (x_pre: Z) (sum: Z) (t: Z) (retval: Z) ,
  [| (retval < 10) |] 
  &&  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < 100000000) |] 
  &&  [| ((-100) <= (sum + (-t) )) |] 
  &&  [| ((sum + (-t) ) <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre 0 (sum + (-t) ) ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_5_3 := 
forall (x_pre: Z) (sum: Z) (p: Z) (t: Z) ,
  [| ((p * 10 ) > t) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (10 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (1 <= p) |] 
  &&  [| (p <= t) |] 
  &&  [| ((INT_MIN + 10 ) <= sum) |] 
  &&  [| (sum <= (INT_MAX - 10 )) |] 
  &&  [| (highest_power10_state x_pre t p sum ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= (t % ( p ) )) |] 
  &&  [| ((t % ( p ) ) < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre (t % ( p ) ) sum ) |]
  &&  emp
.

Definition signed_digit_score_entail_wit_6 := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (t > 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= (t ÷ 10 )) |] 
  &&  [| ((t ÷ 10 ) < 100000000) |] 
  &&  [| ((-100) <= (sum + (t % ( 10 ) ) )) |] 
  &&  [| ((sum + (t % ( 10 ) ) ) <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre (t ÷ 10 ) (sum + (t % ( 10 ) ) ) ) |]
  &&  emp
.

Definition signed_digit_score_return_wit_1 := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (t <= 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| ((-100) <= sum) |] 
  &&  [| (sum <= 100) |] 
  &&  [| (signed_digit_tail_state x_pre t sum ) |]
  &&  emp
|--
  [| (signed_digit_score_result x_pre sum ) |]
  &&  emp
.

Definition signed_digit_score_partial_solve_wit_1_pure := 
forall (x_pre: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |]
  &&  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition signed_digit_score_partial_solve_wit_1_aux := 
forall (x_pre: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |]
  &&  emp
.

Definition signed_digit_score_partial_solve_wit_1 := signed_digit_score_partial_solve_wit_1_pure -> signed_digit_score_partial_solve_wit_1_aux.

Definition signed_digit_score_partial_solve_wit_2_pure := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-t) ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition signed_digit_score_partial_solve_wit_2_aux := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre < 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
.

Definition signed_digit_score_partial_solve_wit_2 := signed_digit_score_partial_solve_wit_2_pure -> signed_digit_score_partial_solve_wit_2_aux.

Definition signed_digit_score_partial_solve_wit_3_pure := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "sum" ) )) # Int  |-> (sum + t ))
  **  ((( &( "msd" ) )) # Int  |-> t)
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition signed_digit_score_partial_solve_wit_3_aux := 
forall (x_pre: Z) (sum: Z) (t: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (t < 10) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre < INT_MAX) |] 
  &&  [| ((Zabs (x_pre)) < 100000000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (t < 100000000) |] 
  &&  [| (sum = 0) |] 
  &&  [| (first_digit_state_145 (Zabs (x_pre)) t ) |]
  &&  emp
.

Definition signed_digit_score_partial_solve_wit_3 := signed_digit_score_partial_solve_wit_3_pure -> signed_digit_score_partial_solve_wit_3_aux.

(*----- Function order_by_points -----*)

Definition order_by_points_safety_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition order_by_points_safety_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| False |]
.

Definition order_by_points_safety_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition order_by_points_safety_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| False |]
.

Definition order_by_points_safety_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 nums_size_pre )
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition order_by_points_safety_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((i + 1 ) = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix (i + 1 ) input_l output_l score_l ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.seg score 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition order_by_points_safety_wit_7 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i >= nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition order_by_points_safety_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_outer_state i input_l output_l score_l ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition order_by_points_safety_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition order_by_points_safety_wit_10 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition order_by_points_safety_wit_11 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition order_by_points_safety_wit_12 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition order_by_points_safety_wit_13 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition order_by_points_safety_wit_14 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition order_by_points_safety_wit_15 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition order_by_points_safety_wit_16 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition order_by_points_safety_wit_17 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition order_by_points_safety_wit_18 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition order_by_points_safety_wit_19 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) <= (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition order_by_points_safety_wit_20 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
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
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition order_by_points_safety_wit_21 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_outer_state (i + 1 ) input_l output_l score_l ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition order_by_points_entail_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  (IntArray.undef_full retval_3 nums_size_pre )
  **  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (0 = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix 0 input_l output_l score_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 nums_size_pre )
  **  (IntArray.seg retval_3 0 0 score_l )
  **  (IntArray.undef_seg retval_3 0 nums_size_pre )
.

Definition order_by_points_entail_wit_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (signed_digit_score_result (Znth i input_l 0) retval ) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l_2))) |] 
  &&  [| (i = (Zlength (score_l_2))) |] 
  &&  [| (order_copy_prefix i input_l output_l_2 score_l_2 ) |]
  &&  (((score + (i * sizeof(INT) ) )) # Int  |-> retval)
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l_2 )
  **  (IntArray.seg score 0 i score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((i + 1 ) = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix (i + 1 ) input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.seg score 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
.

Definition order_by_points_entail_wit_3 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l_2))) |] 
  &&  [| ((i + 1 ) = (Zlength (score_l_2))) |] 
  &&  [| (order_copy_prefix (i + 1 ) input_l output_l_2 score_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l_2 )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.seg score 0 (i + 1 ) score_l_2 )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nums_size_pre) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((i + 1 ) = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix (i + 1 ) input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.seg score 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
.

Definition order_by_points_entail_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i >= nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l_2))) |] 
  &&  [| (i = (Zlength (score_l_2))) |] 
  &&  [| (order_copy_prefix i input_l output_l_2 score_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 i output_l_2 )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.seg score 0 i score_l_2 )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_outer_state 0 input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_entail_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l_2))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l_2))) |] 
  &&  [| (order_sort_outer_state i input_l output_l_2 score_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i 1 input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_entail_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (j >= nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l_2))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l_2))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l_2 score_l_2 ) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_outer_state (i + 1 ) input_l output_l score_l ) |]
  &&  ((( &( "j" ) )) # Int  |-> nums_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_entail_wit_7_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l_2 0) > (Znth j score_l_2 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l_2))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l_2))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l_2 score_l_2 ) |]
  &&  (IntArray.full data nums_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i (j + 1 ) input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_entail_wit_7_2 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l_2 0) <= (Znth j score_l_2 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l_2))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l_2))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l_2 score_l_2 ) |]
  &&  (IntArray.full score nums_size_pre score_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i (j + 1 ) input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_entail_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (score: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l_2))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l_2))) |] 
  &&  [| (order_sort_outer_state (i + 1 ) input_l output_l_2 score_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_outer_state (i + 1 ) input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_entail_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i >= nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l_2))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l_2))) |] 
  &&  [| (order_sort_outer_state i input_l output_l_2 score_l_2 ) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l_2 )
  **  (IntArray.full score nums_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (problem_145_spec_z input_l output_l ) |]
  &&  ((( &( "i" ) )) # Int  |-> nums_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
.

Definition order_by_points_return_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (score_l: (@list Z)) (out: Z) (data_2: Z) (score: Z) ,
  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (nums_size_pre = (Zlength (output_l_2))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (problem_145_spec_z input_l output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data_2 nums_size_pre output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = nums_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_145_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data output_size output_l )
.

Definition order_by_points_partial_solve_wit_1 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_2_pure := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((( &( "score" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (nums_size_pre >= 0) |] 
  &&  [| (nums_size_pre < INT_MAX) |]
.

Definition order_by_points_partial_solve_wit_2_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (nums_size_pre >= 0) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_2 := order_by_points_partial_solve_wit_2_pure -> order_by_points_partial_solve_wit_2_aux.

Definition order_by_points_partial_solve_wit_3_pure := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((( &( "score" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (nums_size_pre >= 0) |] 
  &&  [| (nums_size_pre < INT_MAX) |]
.

Definition order_by_points_partial_solve_wit_3_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| (nums_size_pre >= 0) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |]
  &&  (IntArray.undef_full retval_2 nums_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_3 := order_by_points_partial_solve_wit_3_pure -> order_by_points_partial_solve_wit_3_aux.

Definition order_by_points_partial_solve_wit_4 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
.

Definition order_by_points_partial_solve_wit_5 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i nums_size_pre )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
.

Definition order_by_points_partial_solve_wit_6 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i nums_pre i 0 nums_size_pre input_l )
  **  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
.

Definition order_by_points_partial_solve_wit_7_pure := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  [| ((Zabs ((Znth i input_l 0))) < 100000000) |] 
  &&  [| ((Znth i input_l 0) <= INT_MAX) |] 
  &&  [| ((Znth i input_l 0) < INT_MAX) |] 
  &&  [| (INT_MIN < (Znth i input_l 0)) |]
.

Definition order_by_points_partial_solve_wit_7_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  [| ((Zabs ((Znth i input_l 0))) < 100000000) |] 
  &&  [| ((Znth i input_l 0) <= INT_MAX) |] 
  &&  [| ((Znth i input_l 0) < INT_MAX) |] 
  &&  [| (INT_MIN < (Znth i input_l 0)) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
.

Definition order_by_points_partial_solve_wit_7 := order_by_points_partial_solve_wit_7_pure -> order_by_points_partial_solve_wit_7_aux.

Definition order_by_points_partial_solve_wit_8 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (score: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (signed_digit_score_result (Znth i input_l 0) retval ) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (IntArray.full nums_pre nums_size_pre input_l )
  **  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
  **  (IntArray.undef_seg score i nums_size_pre )
|--
  [| (signed_digit_score_result (Znth i input_l 0) retval ) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nums_size_pre) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (i = (Zlength (score_l))) |] 
  &&  [| (order_copy_prefix i input_l output_l score_l ) |]
  &&  (((score + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg score (i + 1 ) nums_size_pre )
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (i + 1 ) nums_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.seg score 0 i score_l )
.

Definition order_by_points_partial_solve_wit_9 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((score + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i score (j - 1 ) 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_10 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((score + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i score j 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_11 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((score + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i score j 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_12 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((score + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i score (j - 1 ) 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_13 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((score + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i score j 0 nums_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_14 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((score + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i score (j - 1 ) 0 nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
.

Definition order_by_points_partial_solve_wit_15 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.missing_i data j 0 nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_16 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) output_l 0))
  **  (IntArray.missing_i data (j - 1 ) 0 nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_17 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((data + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data j 0 nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_18 := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (score: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (IntArray.full data nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
|--
  [| ((Znth (j - 1 ) score_l 0) > (Znth j score_l 0)) |] 
  &&  [| (j < nums_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_145_pre_z input_l ) |] 
  &&  [| (order_by_points_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < nums_size_pre) |] 
  &&  [| (1 <= j) |] 
  &&  [| (j <= nums_size_pre) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (order_sort_inner_state i j input_l output_l score_l ) |]
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data (j - 1 ) 0 nums_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full score nums_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
.

Definition order_by_points_partial_solve_wit_19_pure := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (score: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (problem_145_spec_z input_l output_l ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  ((( &( "i" ) )) # Int  |-> nums_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |]
.

Definition order_by_points_partial_solve_wit_19_aux := 
forall (nums_size_pre: Z) (nums_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (score: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (problem_145_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> nums_size_pre)
  **  (IntArray.full nums_pre nums_size_pre input_l )
  **  (IntArray.full data nums_size_pre output_l )
  **  (IntArray.full score nums_size_pre score_l )
|--
  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (score <> 0) |] 
  &&  [| (0 <= nums_size_pre) |] 
  &&  [| (nums_size_pre < INT_MAX) |] 
  &&  [| (nums_size_pre = (Zlength (input_l))) |] 
  &&  [| (nums_size_pre = (Zlength (output_l))) |] 
  &&  [| (nums_size_pre = (Zlength (score_l))) |] 
  &&  [| (problem_145_spec_z input_l output_l ) |]
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
Axiom proof_of_signed_digit_score_safety_wit_26 : signed_digit_score_safety_wit_26.
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
Axiom proof_of_order_by_points_entail_wit_7_1 : order_by_points_entail_wit_7_1.
Axiom proof_of_order_by_points_entail_wit_7_2 : order_by_points_entail_wit_7_2.
Axiom proof_of_order_by_points_entail_wit_8 : order_by_points_entail_wit_8.
Axiom proof_of_order_by_points_entail_wit_9 : order_by_points_entail_wit_9.
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
