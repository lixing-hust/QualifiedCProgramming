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
Require Import coins_84.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function solve -----*)

Definition solve_safety_wit_1 := 
forall (N_pre: Z) ,
  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_2 := 
forall (N_pre: Z) ,
  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "out_zero" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solve_safety_wit_3 := 
forall (N_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (CharArray.undef_full retval 2 )
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_4 := 
forall (N_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (CharArray.undef_full retval 2 )
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition solve_safety_wit_5 := 
forall (N_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_6 := 
forall (N_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_7 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_8 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_9 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "orig" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_10 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "bits" ) )) # Int  |->_)
  **  ((( &( "orig" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_11 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "orig" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_12 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "orig" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_13 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "orig" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_14 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "orig" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_15 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_16 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((sum + (x % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (x % ( 10 ) ) )) |]
.

Definition solve_safety_wit_17 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((x <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition solve_safety_wit_18 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition solve_safety_wit_19 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (x % ( 10 ) ) ))
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((x <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition solve_safety_wit_20 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (x % ( 10 ) ) ))
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition solve_safety_wit_21 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_22 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) ,
  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  ((( &( "out_zero" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solve_safety_wit_23 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (CharArray.undef_full retval 2 )
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_24 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (CharArray.undef_full retval 2 )
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition solve_safety_wit_25 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_26 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_27 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_28 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((bits + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bits + 1 )) |]
.

Definition solve_safety_wit_29 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_30 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((t <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition solve_safety_wit_31 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solve_safety_wit_32 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((bits + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bits + 1 )) |]
.

Definition solve_safety_wit_33 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_34 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  (CharArray.undef_full retval (bits + 1 ) )
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_35 := 
forall (N_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_36 := 
forall (N_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_37 := 
forall (N_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num bits out_l ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_38 := 
forall (N_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num bits out_l ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((bits - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bits - 1 )) |]
.

Definition solve_safety_wit_39 := 
forall (N_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num bits out_l ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_40 := 
forall (N_pre: Z) (out_l: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((48 + (num % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (48 + (num % ( 2 ) ) )) |]
.

Definition solve_safety_wit_41 := 
forall (N_pre: Z) (out_l: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((num <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition solve_safety_wit_42 := 
forall (N_pre: Z) (out_l: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition solve_safety_wit_43 := 
forall (N_pre: Z) (out_l: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solve_safety_wit_44 := 
forall (N_pre: Z) (out_l: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (replace_Znth (bits) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l) ((cons (0) (nil)))))) )
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((num <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition solve_safety_wit_45 := 
forall (N_pre: Z) (out_l: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (replace_Znth (bits) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l) ((cons (0) (nil)))))) )
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solve_entail_wit_1 := 
forall (N_pre: Z) ,
  [| (N_pre <> 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  emp
|--
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= N_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 10000) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (decimal_sum_state_z N_pre N_pre 0 ) |]
  &&  emp
.

Definition solve_entail_wit_2 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  emp
|--
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= (x ÷ 10 )) |] 
  &&  [| ((x ÷ 10 ) <= N_pre) |] 
  &&  [| (0 <= (sum + (x % ( 10 ) ) )) |] 
  &&  [| ((sum + (x % ( 10 ) ) ) <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre (x ÷ 10 ) (sum + (x % ( 10 ) ) ) ) |]
  &&  emp
.

Definition solve_entail_wit_3 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (t: Z) (bits: Z) (orig: Z) (num: Z) (sum: Z) (x: Z) ,
  [| (x <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= N_pre) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_state_z N_pre x sum ) |]
  &&  emp
|--
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  emp
.

Definition solve_entail_wit_4 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) ,
  [| (sum <> 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  emp
|--
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = sum) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (sum = sum) |] 
  &&  [| (0 < sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z sum sum bits ) |]
  &&  emp
.

Definition solve_entail_wit_5 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  emp
|--
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= (t ÷ 2 )) |] 
  &&  [| (0 <= (bits + 1 )) |] 
  &&  [| ((bits + 1 ) < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num (t ÷ 2 ) (bits + 1 ) ) |]
  &&  emp
.

Definition solve_entail_wit_6 := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  (CharArray.undef_full retval (bits + 1 ) )
|--
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (bits = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = bits) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (bits + 1 )) |]
  &&  (CharArray.full retval 0 (repeat_Z (0) (0)) )
  **  (CharArray.undef_seg retval 0 (bits + 1 ) )
.

Definition solve_entail_wit_7 := 
forall (N_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
|--
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (total + 1 )) |]
  &&  (CharArray.full out (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
.

Definition solve_entail_wit_8 := 
forall (N_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (i > total) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z num num bits out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_entail_wit_9 := 
forall (N_pre: Z) (out_l_2: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z num num bits out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num bits out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_entail_wit_10 := 
forall (N_pre: Z) (out: Z) (out_l_2: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num bits out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= (bits - 1 )) |] 
  &&  [| ((bits - 1 ) < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num ((bits - 1 ) + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_entail_wit_11 := 
forall (N_pre: Z) (out_l_2: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (replace_Znth (bits) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l_2) ((cons (0) (nil)))))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= (num ÷ 2 )) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig (num ÷ 2 ) bits out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_return_wit_1 := 
forall (N_pre: Z) (out: Z) (out_l_2: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (num <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num bits out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (1 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_84_spec_z N_pre out_l ) |]
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_return_wit_2 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 2 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (1 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_84_spec_z N_pre out_l ) |]
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_return_wit_3 := 
forall (N_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 2 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (1 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_84_spec_z N_pre out_l ) |]
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_partial_solve_wit_1_pure := 
forall (N_pre: Z) ,
  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  ((( &( "out_zero" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  [| (2 > 0) |]
.

Definition solve_partial_solve_wit_1_aux := 
forall (N_pre: Z) ,
  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  emp
|--
  [| (2 > 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  emp
.

Definition solve_partial_solve_wit_1 := solve_partial_solve_wit_1_pure -> solve_partial_solve_wit_1_aux.

Definition solve_partial_solve_wit_2 := 
forall (N_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (CharArray.undef_full retval 2 )
|--
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 2 )
.

Definition solve_partial_solve_wit_3 := 
forall (N_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  [| (retval <> 0) |] 
  &&  [| (N_pre = 0) |] 
  &&  [| (0 <= N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (problem_84_pre_z N_pre ) |]
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
.

Definition solve_partial_solve_wit_4_pure := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) ,
  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  ((( &( "out_zero" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (2 > 0) |]
.

Definition solve_partial_solve_wit_4_aux := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) ,
  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  emp
|--
  [| (2 > 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  emp
.

Definition solve_partial_solve_wit_4 := solve_partial_solve_wit_4_pure -> solve_partial_solve_wit_4_aux.

Definition solve_partial_solve_wit_5 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (CharArray.undef_full retval 2 )
|--
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 2 )
.

Definition solve_partial_solve_wit_6 := 
forall (N_pre: Z) (x: Z) (sum: Z) (num: Z) (orig: Z) (bits: Z) (t: Z) (total: Z) (i: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  [| (retval <> 0) |] 
  &&  [| (sum = 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= 10000) |] 
  &&  [| (num = 0) |] 
  &&  [| (orig = 0) |] 
  &&  [| (bits = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |]
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
.

Definition solve_partial_solve_wit_7_pure := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  ((( &( "N" ) )) # Int  |-> N_pre)
  **  ((( &( "origN" ) )) # Int  |-> N_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((bits + 1 ) > 0) |]
.

Definition solve_partial_solve_wit_7_aux := 
forall (N_pre: Z) (out: Z) (i: Z) (total: Z) (bits: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  emp
|--
  [| ((bits + 1 ) > 0) |] 
  &&  [| (t <= 0) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t bits ) |]
  &&  emp
.

Definition solve_partial_solve_wit_7 := solve_partial_solve_wit_7_pure -> solve_partial_solve_wit_7_aux.

Definition solve_partial_solve_wit_8 := 
forall (N_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (t: Z) (num: Z) (orig: Z) (sum: Z) (x: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  [| (i <= total) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num <= 10000) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (total + 1 ) )
  **  (CharArray.full out i (repeat_Z (0) (i)) )
.

Definition solve_partial_solve_wit_9 := 
forall (N_pre: Z) (out_l: (@list Z)) (x: Z) (sum: Z) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < N_pre) |] 
  &&  [| (N_pre <= 10000) |] 
  &&  [| (x = 0) |] 
  &&  [| (sum = orig) |] 
  &&  [| (decimal_sum_value_z N_pre sum ) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig <= 10000) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (((out + (bits * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out bits 0 (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_solve_safety_wit_1 : solve_safety_wit_1.
Axiom proof_of_solve_safety_wit_2 : solve_safety_wit_2.
Axiom proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Axiom proof_of_solve_safety_wit_4 : solve_safety_wit_4.
Axiom proof_of_solve_safety_wit_5 : solve_safety_wit_5.
Axiom proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Axiom proof_of_solve_safety_wit_7 : solve_safety_wit_7.
Axiom proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Axiom proof_of_solve_safety_wit_9 : solve_safety_wit_9.
Axiom proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Axiom proof_of_solve_safety_wit_11 : solve_safety_wit_11.
Axiom proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Axiom proof_of_solve_safety_wit_13 : solve_safety_wit_13.
Axiom proof_of_solve_safety_wit_14 : solve_safety_wit_14.
Axiom proof_of_solve_safety_wit_15 : solve_safety_wit_15.
Axiom proof_of_solve_safety_wit_16 : solve_safety_wit_16.
Axiom proof_of_solve_safety_wit_17 : solve_safety_wit_17.
Axiom proof_of_solve_safety_wit_18 : solve_safety_wit_18.
Axiom proof_of_solve_safety_wit_19 : solve_safety_wit_19.
Axiom proof_of_solve_safety_wit_20 : solve_safety_wit_20.
Axiom proof_of_solve_safety_wit_21 : solve_safety_wit_21.
Axiom proof_of_solve_safety_wit_22 : solve_safety_wit_22.
Axiom proof_of_solve_safety_wit_23 : solve_safety_wit_23.
Axiom proof_of_solve_safety_wit_24 : solve_safety_wit_24.
Axiom proof_of_solve_safety_wit_25 : solve_safety_wit_25.
Axiom proof_of_solve_safety_wit_26 : solve_safety_wit_26.
Axiom proof_of_solve_safety_wit_27 : solve_safety_wit_27.
Axiom proof_of_solve_safety_wit_28 : solve_safety_wit_28.
Axiom proof_of_solve_safety_wit_29 : solve_safety_wit_29.
Axiom proof_of_solve_safety_wit_30 : solve_safety_wit_30.
Axiom proof_of_solve_safety_wit_31 : solve_safety_wit_31.
Axiom proof_of_solve_safety_wit_32 : solve_safety_wit_32.
Axiom proof_of_solve_safety_wit_33 : solve_safety_wit_33.
Axiom proof_of_solve_safety_wit_34 : solve_safety_wit_34.
Axiom proof_of_solve_safety_wit_35 : solve_safety_wit_35.
Axiom proof_of_solve_safety_wit_36 : solve_safety_wit_36.
Axiom proof_of_solve_safety_wit_37 : solve_safety_wit_37.
Axiom proof_of_solve_safety_wit_38 : solve_safety_wit_38.
Axiom proof_of_solve_safety_wit_39 : solve_safety_wit_39.
Axiom proof_of_solve_safety_wit_40 : solve_safety_wit_40.
Axiom proof_of_solve_safety_wit_41 : solve_safety_wit_41.
Axiom proof_of_solve_safety_wit_42 : solve_safety_wit_42.
Axiom proof_of_solve_safety_wit_43 : solve_safety_wit_43.
Axiom proof_of_solve_safety_wit_44 : solve_safety_wit_44.
Axiom proof_of_solve_safety_wit_45 : solve_safety_wit_45.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Axiom proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Axiom proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Axiom proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Axiom proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Axiom proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_return_wit_2 : solve_return_wit_2.
Axiom proof_of_solve_return_wit_3 : solve_return_wit_3.
Axiom proof_of_solve_partial_solve_wit_1_pure : solve_partial_solve_wit_1_pure.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.
Axiom proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2.
Axiom proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3.
Axiom proof_of_solve_partial_solve_wit_4_pure : solve_partial_solve_wit_4_pure.
Axiom proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4.
Axiom proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5.
Axiom proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6.
Axiom proof_of_solve_partial_solve_wit_7_pure : solve_partial_solve_wit_7_pure.
Axiom proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7.
Axiom proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8.
Axiom proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9.

End VC_Correct.
