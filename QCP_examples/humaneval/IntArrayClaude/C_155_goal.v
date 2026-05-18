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
Require Import coins_155.
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

(*----- Function even_odd_count -----*)

Definition even_odd_count_safety_wit_1 := 
forall (num_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (num_pre))) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  ((( &( "n2" ) )) # Int  |->_)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition even_odd_count_safety_wit_2 := 
forall (num_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (num_pre))) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition even_odd_count_safety_wit_3 := 
forall (num_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (num_pre))) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition even_odd_count_safety_wit_4 := 
forall (num_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (num_pre))) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition even_odd_count_safety_wit_5 := 
forall (num_pre: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (Zabs (num_pre))) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition even_odd_count_safety_wit_6 := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition even_odd_count_safety_wit_7 := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| ((w <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition even_odd_count_safety_wit_8 := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition even_odd_count_safety_wit_9 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  [| (((w % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition even_odd_count_safety_wit_10 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition even_odd_count_safety_wit_11 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition even_odd_count_safety_wit_12 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (((w % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  [| ((n1 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n1 + 1 )) |]
.

Definition even_odd_count_safety_wit_13 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (((w % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition even_odd_count_safety_wit_14 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (((w % ( 10 ) ) % ( 2 ) ) <> 1) |] 
  &&  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  [| ((n2 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n2 + 1 )) |]
.

Definition even_odd_count_safety_wit_15 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (((w % ( 10 ) ) % ( 2 ) ) <> 1) |] 
  &&  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition even_odd_count_safety_wit_16 := 
forall (num_pre: Z) (w: Z) (d: Z) (n1: Z) (n2: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (d = (w % ( 10 ) )) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
|--
  [| ((w <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition even_odd_count_safety_wit_17 := 
forall (num_pre: Z) (w: Z) (d: Z) (n1: Z) (n2: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (d = (w % ( 10 ) )) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition even_odd_count_safety_wit_18 := 
forall (num_pre: Z) (w: Z) (d: Z) (n1: Z) (n2: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (d = (w % ( 10 ) )) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
|--
  [| ((w <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition even_odd_count_safety_wit_19 := 
forall (num_pre: Z) (w: Z) (d: Z) (n1: Z) (n2: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (d = (w % ( 10 ) )) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition even_odd_count_safety_wit_20 := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition even_odd_count_safety_wit_21 := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition even_odd_count_safety_wit_22 := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition even_odd_count_safety_wit_23 := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition even_odd_count_entail_wit_1_1 := 
forall (num_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (Zabs (num_pre))) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  emp
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre retval 0 0 ) |]
  &&  emp
.

Definition even_odd_count_entail_wit_1_2 := 
forall (num_pre: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (Zabs (num_pre))) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  emp
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < INT_MAX) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre retval 1 0 ) |]
  &&  emp
.

Definition even_odd_count_entail_wit_2 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (((w % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  emp
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| ((w % ( 10 ) ) = (w % ( 10 ) )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| ((n1 + 1 ) < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 (n1 + 1 ) ) |]
  &&  emp
.

Definition even_odd_count_entail_wit_3 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (((w % ( 10 ) ) % ( 2 ) ) <> 1) |] 
  &&  [| (w > 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  emp
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| ((w % ( 10 ) ) = (w % ( 10 ) )) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= (n2 + 1 )) |] 
  &&  [| ((n2 + 1 ) < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) (n2 + 1 ) n1 ) |]
  &&  emp
.

Definition even_odd_count_entail_wit_4_1 := 
forall (num_pre: Z) (w: Z) (d: Z) (n1: Z) (n2: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (d = (w % ( 10 ) )) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  emp
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= (w ÷ 10 )) |] 
  &&  [| ((w ÷ 10 ) <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  emp
.

Definition even_odd_count_entail_wit_4_2 := 
forall (num_pre: Z) (w: Z) (d: Z) (n1: Z) (n2: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 < w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (d = (w % ( 10 ) )) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  emp
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= (w ÷ 10 )) |] 
  &&  [| ((w ÷ 10 ) <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre (w ÷ 10 ) n2 n1 ) |]
  &&  emp
.

Definition even_odd_count_return_wit_1 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> n1)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (retval <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_155_spec_z num_pre output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
.

Definition even_odd_count_partial_solve_wit_1_pure := 
forall (num_pre: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre <= INT_MAX) |]
.

Definition even_odd_count_partial_solve_wit_1_aux := 
forall (num_pre: Z) ,
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  emp
|--
  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |]
  &&  emp
.

Definition even_odd_count_partial_solve_wit_1 := even_odd_count_partial_solve_wit_1_pure -> even_odd_count_partial_solve_wit_1_aux.

Definition even_odd_count_partial_solve_wit_2 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) ,
  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  emp
|--
  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  emp
.

Definition even_odd_count_partial_solve_wit_3_pure := 
forall (num_pre: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |]
.

Definition even_odd_count_partial_solve_wit_3_aux := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition even_odd_count_partial_solve_wit_3 := even_odd_count_partial_solve_wit_3_pure -> even_odd_count_partial_solve_wit_3_aux.

Definition even_odd_count_partial_solve_wit_4 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition even_odd_count_partial_solve_wit_5 := 
forall (num_pre: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (w <= 0) |] 
  &&  [| (INT_MIN < num_pre) |] 
  &&  [| (num_pre < INT_MAX) |] 
  &&  [| (((Zabs (num_pre)) + 1 ) < INT_MAX) |] 
  &&  [| (problem_155_pre_z num_pre ) |] 
  &&  [| (0 <= w) |] 
  &&  [| (w <= INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| (0 <= n2) |] 
  &&  [| (n2 < INT_MAX) |] 
  &&  [| (digit_count_state num_pre w n2 n1 ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_even_odd_count_safety_wit_1 : even_odd_count_safety_wit_1.
Axiom proof_of_even_odd_count_safety_wit_2 : even_odd_count_safety_wit_2.
Axiom proof_of_even_odd_count_safety_wit_3 : even_odd_count_safety_wit_3.
Axiom proof_of_even_odd_count_safety_wit_4 : even_odd_count_safety_wit_4.
Axiom proof_of_even_odd_count_safety_wit_5 : even_odd_count_safety_wit_5.
Axiom proof_of_even_odd_count_safety_wit_6 : even_odd_count_safety_wit_6.
Axiom proof_of_even_odd_count_safety_wit_7 : even_odd_count_safety_wit_7.
Axiom proof_of_even_odd_count_safety_wit_8 : even_odd_count_safety_wit_8.
Axiom proof_of_even_odd_count_safety_wit_9 : even_odd_count_safety_wit_9.
Axiom proof_of_even_odd_count_safety_wit_10 : even_odd_count_safety_wit_10.
Axiom proof_of_even_odd_count_safety_wit_11 : even_odd_count_safety_wit_11.
Axiom proof_of_even_odd_count_safety_wit_12 : even_odd_count_safety_wit_12.
Axiom proof_of_even_odd_count_safety_wit_13 : even_odd_count_safety_wit_13.
Axiom proof_of_even_odd_count_safety_wit_14 : even_odd_count_safety_wit_14.
Axiom proof_of_even_odd_count_safety_wit_15 : even_odd_count_safety_wit_15.
Axiom proof_of_even_odd_count_safety_wit_16 : even_odd_count_safety_wit_16.
Axiom proof_of_even_odd_count_safety_wit_17 : even_odd_count_safety_wit_17.
Axiom proof_of_even_odd_count_safety_wit_18 : even_odd_count_safety_wit_18.
Axiom proof_of_even_odd_count_safety_wit_19 : even_odd_count_safety_wit_19.
Axiom proof_of_even_odd_count_safety_wit_20 : even_odd_count_safety_wit_20.
Axiom proof_of_even_odd_count_safety_wit_21 : even_odd_count_safety_wit_21.
Axiom proof_of_even_odd_count_safety_wit_22 : even_odd_count_safety_wit_22.
Axiom proof_of_even_odd_count_safety_wit_23 : even_odd_count_safety_wit_23.
Axiom proof_of_even_odd_count_entail_wit_1_1 : even_odd_count_entail_wit_1_1.
Axiom proof_of_even_odd_count_entail_wit_1_2 : even_odd_count_entail_wit_1_2.
Axiom proof_of_even_odd_count_entail_wit_2 : even_odd_count_entail_wit_2.
Axiom proof_of_even_odd_count_entail_wit_3 : even_odd_count_entail_wit_3.
Axiom proof_of_even_odd_count_entail_wit_4_1 : even_odd_count_entail_wit_4_1.
Axiom proof_of_even_odd_count_entail_wit_4_2 : even_odd_count_entail_wit_4_2.
Axiom proof_of_even_odd_count_return_wit_1 : even_odd_count_return_wit_1.
Axiom proof_of_even_odd_count_partial_solve_wit_1_pure : even_odd_count_partial_solve_wit_1_pure.
Axiom proof_of_even_odd_count_partial_solve_wit_1 : even_odd_count_partial_solve_wit_1.
Axiom proof_of_even_odd_count_partial_solve_wit_2 : even_odd_count_partial_solve_wit_2.
Axiom proof_of_even_odd_count_partial_solve_wit_3_pure : even_odd_count_partial_solve_wit_3_pure.
Axiom proof_of_even_odd_count_partial_solve_wit_3 : even_odd_count_partial_solve_wit_3.
Axiom proof_of_even_odd_count_partial_solve_wit_4 : even_odd_count_partial_solve_wit_4.
Axiom proof_of_even_odd_count_partial_solve_wit_5 : even_odd_count_partial_solve_wit_5.

End VC_Correct.
