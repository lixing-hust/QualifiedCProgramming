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
Require Import coins_123.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function get_odd_collatz -----*)

Definition get_odd_collatz_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_2 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (problem_123_pre_z n0 )) (PreH2 : (collatz_safe_123 n0 )) (PreH3 : (0 < cur)) (PreH4 : (cur < INT_MAX)) (PreH5 : (0 < count)) (PreH6 : (count < INT_MAX)) (PreH7 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_3 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (cur <> 1)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (0 < cur)) (PreH5 : (cur < INT_MAX)) (PreH6 : (0 < count)) (PreH7 : (count < INT_MAX)) (PreH8 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((cur <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition get_odd_collatz_safety_wit_4 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (cur <> 1)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (0 < cur)) (PreH5 : (cur < INT_MAX)) (PreH6 : (0 < count)) (PreH7 : (count < INT_MAX)) (PreH8 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_odd_collatz_safety_wit_5 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (cur <> 1)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (0 < cur)) (PreH5 : (cur < INT_MAX)) (PreH6 : (0 < count)) (PreH7 : (count < INT_MAX)) (PreH8 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_6 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition get_odd_collatz_safety_wit_7 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_8 := 
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (((3 * cur ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((3 * cur ) + 1 )) ”
) \/
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (((3 * cur ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((3 * cur ) + 1 )) ”
).

Definition get_odd_collatz_safety_wit_8_split_goal_1 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (((3 * cur ) + 1 ) <= INT_MAX) ”
.

Definition get_odd_collatz_safety_wit_8_split_goal_2 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((INT_MIN) <= ((3 * cur ) + 1 )) ”
.

Definition get_odd_collatz_safety_wit_9 := 
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((3 * cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (3 * cur )) ”
) \/
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((3 * cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (3 * cur )) ”
).

Definition get_odd_collatz_safety_wit_9_split_goal_1 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((3 * cur ) <= INT_MAX) ”
.

Definition get_odd_collatz_safety_wit_9_split_goal_2 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((INT_MIN) <= (3 * cur )) ”
.

Definition get_odd_collatz_safety_wit_10 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition get_odd_collatz_safety_wit_11 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_12 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((cur <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition get_odd_collatz_safety_wit_13 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_odd_collatz_safety_wit_14 := 
forall (n0: Z) (count: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (collatz_final_count_123 n0 count )) (PreH5 : (0 < count)) (PreH6 : ((count + 1 ) < INT_MAX)) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cur" ) )) # Int  |-> n0)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition get_odd_collatz_safety_wit_15 := 
forall (n0: Z) (count: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (collatz_final_count_123 n0 count )) (PreH5 : (0 < count)) (PreH6 : ((count + 1 ) < INT_MAX)) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cur" ) )) # Int  |-> n0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_16 := 
forall (n0: Z) (count: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (0 < count)) (PreH7 : ((count + 1 ) < INT_MAX)) ,
  (IntArray.undef_full retval_2 (count + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((( &( "cap" ) )) # Int  |-> (count + 1 ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cur" ) )) # Int  |-> n0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_odd_collatz_safety_wit_17 := 
forall (n0: Z) (count: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (0 < count)) (PreH7 : ((count + 1 ) < INT_MAX)) ,
  (IntArray.undef_full retval_2 (count + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((( &( "cap" ) )) # Int  |-> (count + 1 ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cur" ) )) # Int  |-> n0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_18 := 
forall (n0: Z) (count: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (0 < count)) (PreH7 : ((count + 1 ) < INT_MAX)) ,
  ((( &( "size" ) )) # Int  |->_)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (count + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((( &( "cap" ) )) # Int  |-> (count + 1 ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cur" ) )) # Int  |-> n0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_19 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (0 < cur)) (PreH8 : (cur < INT_MAX)) (PreH9 : (0 < count)) (PreH10 : ((count + 1 ) < INT_MAX)) (PreH11 : (1 <= size)) (PreH12 : (size <= count)) (PreH13 : (size = (Zlength (output_l)))) (PreH14 : (collatz_output_state_123 n0 count cur output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_20 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (cur <> 1)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (problem_123_pre_z n0 )) (PreH5 : (collatz_safe_123 n0 )) (PreH6 : (collatz_final_count_123 n0 count )) (PreH7 : (cap = (count + 1 ))) (PreH8 : (0 < cur)) (PreH9 : (cur < INT_MAX)) (PreH10 : (0 < count)) (PreH11 : ((count + 1 ) < INT_MAX)) (PreH12 : (1 <= size)) (PreH13 : (size <= count)) (PreH14 : (size = (Zlength (output_l)))) (PreH15 : (collatz_output_state_123 n0 count cur output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((cur <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition get_odd_collatz_safety_wit_21 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (cur <> 1)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (problem_123_pre_z n0 )) (PreH5 : (collatz_safe_123 n0 )) (PreH6 : (collatz_final_count_123 n0 count )) (PreH7 : (cap = (count + 1 ))) (PreH8 : (0 < cur)) (PreH9 : (cur < INT_MAX)) (PreH10 : (0 < count)) (PreH11 : ((count + 1 ) < INT_MAX)) (PreH12 : (1 <= size)) (PreH13 : (size <= count)) (PreH14 : (size = (Zlength (output_l)))) (PreH15 : (collatz_output_state_123 n0 count cur output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_odd_collatz_safety_wit_22 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (cur <> 1)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (problem_123_pre_z n0 )) (PreH5 : (collatz_safe_123 n0 )) (PreH6 : (collatz_final_count_123 n0 count )) (PreH7 : (cap = (count + 1 ))) (PreH8 : (0 < cur)) (PreH9 : (cur < INT_MAX)) (PreH10 : (0 < count)) (PreH11 : ((count + 1 ) < INT_MAX)) (PreH12 : (1 <= size)) (PreH13 : (size <= count)) (PreH14 : (size = (Zlength (output_l)))) (PreH15 : (collatz_output_state_123 n0 count cur output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_23 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (size + 1 )) ”
.

Definition get_odd_collatz_safety_wit_24 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_25 := 
(
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (((3 * cur ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((3 * cur ) + 1 )) ”
) \/
(
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (((3 * cur ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((3 * cur ) + 1 )) ”
).

Definition get_odd_collatz_safety_wit_25_split_goal_1 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (((3 * cur ) + 1 ) <= INT_MAX) ”
.

Definition get_odd_collatz_safety_wit_25_split_goal_2 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((INT_MIN) <= ((3 * cur ) + 1 )) ”
.

Definition get_odd_collatz_safety_wit_26 := 
(
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((3 * cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (3 * cur )) ”
) \/
(
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((3 * cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (3 * cur )) ”
).

Definition get_odd_collatz_safety_wit_26_split_goal_1 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((3 * cur ) <= INT_MAX) ”
.

Definition get_odd_collatz_safety_wit_26_split_goal_2 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((INT_MIN) <= (3 * cur )) ”
.

Definition get_odd_collatz_safety_wit_27 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition get_odd_collatz_safety_wit_28 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_safety_wit_29 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((cur <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition get_odd_collatz_safety_wit_30 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_odd_collatz_safety_wit_31 := 
forall (n0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (size = count)) (PreH8 : (size = (Zlength (output_l)))) (PreH9 : (collatz_output_state_123 n0 count 1 output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_odd_collatz_entail_wit_1 := 
(
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 < INT_MAX) ” 
  &&  “ (collatz_count_state_123 n0 n_pre 1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
) \/
(
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) ,
  TT && emp 
|--
  “ (collatz_count_state_123 n0 n_pre 1 ) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < n_pre) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) ,
  TT && emp 
|--
  “ (collatz_count_state_123 n0 n_pre 1 ) ”
.

Definition get_odd_collatz_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) ,
  TT && emp 
|--
  “ (n_pre < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) ,
  TT && emp 
|--
  “ (0 < n_pre) ”
.

Definition get_odd_collatz_entail_wit_2_1 := 
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (0 < ((3 * cur ) + 1 )) ” 
  &&  “ (((3 * cur ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < (count + 1 )) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (collatz_count_state_123 n0 ((3 * cur ) + 1 ) (count + 1 ) ) ”
  &&  emp
) \/
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (collatz_count_state_123 n0 ((3 * cur ) + 1 ) (count + 1 ) ) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (((3 * cur ) + 1 ) < INT_MAX) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_2_1_split_goal_1 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (collatz_count_state_123 n0 ((3 * cur ) + 1 ) (count + 1 ) ) ”
.

Definition get_odd_collatz_entail_wit_2_1_split_goal_2 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ ((count + 1 ) < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_2_1_split_goal_3 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (((3 * cur ) + 1 ) < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_2_2 := 
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (0 < (cur ÷ 2 )) ” 
  &&  “ ((cur ÷ 2 ) < INT_MAX) ” 
  &&  “ (0 < count) ” 
  &&  “ (count < INT_MAX) ” 
  &&  “ (collatz_count_state_123 n0 (cur ÷ 2 ) count ) ”
  &&  emp
) \/
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (collatz_count_state_123 n0 (cur ÷ 2 ) count ) ” 
  &&  “ ((cur ÷ 2 ) < INT_MAX) ” 
  &&  “ (0 < (cur ÷ 2 )) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_2_2_split_goal_1 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (collatz_count_state_123 n0 (cur ÷ 2 ) count ) ”
.

Definition get_odd_collatz_entail_wit_2_2_split_goal_2 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ ((cur ÷ 2 ) < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_2_2_split_goal_3 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (0 < cur)) (PreH6 : (cur < INT_MAX)) (PreH7 : (0 < count)) (PreH8 : (count < INT_MAX)) (PreH9 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (0 < (cur ÷ 2 )) ”
.

Definition get_odd_collatz_entail_wit_3 := 
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (cur = 1)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (0 < cur)) (PreH5 : (cur < INT_MAX)) (PreH6 : (0 < count)) (PreH7 : (count < INT_MAX)) (PreH8 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ”
  &&  emp
) \/
(
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (cur = 1)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (0 < cur)) (PreH5 : (cur < INT_MAX)) (PreH6 : (0 < count)) (PreH7 : (count < INT_MAX)) (PreH8 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (collatz_final_count_123 n0 count ) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_3_split_goal_1 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (cur = 1)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (0 < cur)) (PreH5 : (cur < INT_MAX)) (PreH6 : (0 < count)) (PreH7 : (count < INT_MAX)) (PreH8 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ ((count + 1 ) < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_3_split_goal_2 := 
forall (n0: Z) (count: Z) (cur: Z) (PreH1 : (cur = 1)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (0 < cur)) (PreH5 : (cur < INT_MAX)) (PreH6 : (0 < count)) (PreH7 : (count < INT_MAX)) (PreH8 : (collatz_count_state_123 n0 cur count )) ,
  TT && emp 
|--
  “ (collatz_final_count_123 n0 count ) ”
.

Definition get_odd_collatz_entail_wit_4 := 
(
forall (n0: Z) (count: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (0 < count)) (PreH7 : ((count + 1 ) < INT_MAX)) ,
  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (count + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ ((count + 1 ) = (count + 1 )) ” 
  &&  “ (0 < n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= count) ” 
  &&  “ (1 = (Zlength (output_l))) ” 
  &&  “ (collatz_output_state_123 n0 count n0 output_l ) ”
  &&  (IntArray.seg retval_2 0 1 output_l )
  **  (IntArray.undef_seg retval_2 1 (count + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
) \/
(
forall (n0: Z) (count: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (0 < count)) (PreH9 : ((count + 1 ) < INT_MAX)) ,
  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
|--
  EX (output_l: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (0 < n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= count) ” 
  &&  “ (1 = (Zlength (output_l))) ” 
  &&  “ (collatz_output_state_123 n0 count n0 output_l ) ”
  &&  (IntArray.seg retval_2 0 1 output_l )
).

Definition get_odd_collatz_entail_wit_5_1 := 
(
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  (IntArray.seg data 0 (size + 1 ) (app (output_l_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (cap = (count + 1 )) ” 
  &&  “ (0 < ((3 * cur ) + 1 )) ” 
  &&  “ (((3 * cur ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (1 <= (size + 1 )) ” 
  &&  “ ((size + 1 ) <= count) ” 
  &&  “ ((size + 1 ) = (Zlength (output_l))) ” 
  &&  “ (collatz_output_state_123 n0 count ((3 * cur ) + 1 ) output_l ) ”
  &&  (IntArray.seg data 0 (size + 1 ) output_l )
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
) \/
(
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (collatz_output_state_123 n0 count ((3 * cur ) + 1 ) (app (output_l_2) ((cons (cur) ((@nil Z))))) ) ” 
  &&  “ ((size + 1 ) = (Zlength ((app (output_l_2) ((cons (cur) ((@nil Z)))))))) ” 
  &&  “ ((size + 1 ) <= count) ” 
  &&  “ (((3 * cur ) + 1 ) < INT_MAX) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_5_1_split_goal_1 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (collatz_output_state_123 n0 count ((3 * cur ) + 1 ) (app (output_l_2) ((cons (cur) ((@nil Z))))) ) ”
.

Definition get_odd_collatz_entail_wit_5_1_split_goal_2 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ ((size + 1 ) = (Zlength ((app (output_l_2) ((cons (cur) ((@nil Z)))))))) ”
.

Definition get_odd_collatz_entail_wit_5_1_split_goal_3 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ ((size + 1 ) <= count) ”
.

Definition get_odd_collatz_entail_wit_5_1_split_goal_4 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (((3 * cur ) + 1 ) < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_5_2 := 
(
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  (IntArray.seg data 0 size output_l_2 )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (cap = (count + 1 )) ” 
  &&  “ (0 < (cur ÷ 2 )) ” 
  &&  “ ((cur ÷ 2 ) < INT_MAX) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (1 <= size) ” 
  &&  “ (size <= count) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (collatz_output_state_123 n0 count (cur ÷ 2 ) output_l ) ”
  &&  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
) \/
(
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (collatz_output_state_123 n0 count (cur ÷ 2 ) output_l_2 ) ” 
  &&  “ ((cur ÷ 2 ) < INT_MAX) ” 
  &&  “ (0 < (cur ÷ 2 )) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_5_2_split_goal_1 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (collatz_output_state_123 n0 count (cur ÷ 2 ) output_l_2 ) ”
.

Definition get_odd_collatz_entail_wit_5_2_split_goal_2 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ ((cur ÷ 2 ) < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_5_2_split_goal_3 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) <> 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l_2)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (0 < (cur ÷ 2 )) ”
.

Definition get_odd_collatz_entail_wit_6 := 
(
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (cur = 1)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (problem_123_pre_z n0 )) (PreH5 : (collatz_safe_123 n0 )) (PreH6 : (collatz_final_count_123 n0 count )) (PreH7 : (cap = (count + 1 ))) (PreH8 : (0 < cur)) (PreH9 : (cur < INT_MAX)) (PreH10 : (0 < count)) (PreH11 : ((count + 1 ) < INT_MAX)) (PreH12 : (1 <= size)) (PreH13 : (size <= count)) (PreH14 : (size = (Zlength (output_l_2)))) (PreH15 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  ((( &( "cur" ) )) # Int  |-> cur)
  **  (IntArray.seg data 0 size output_l_2 )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (cap = (count + 1 )) ” 
  &&  “ (size = count) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (collatz_output_state_123 n0 count 1 output_l ) ”
  &&  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
) \/
(
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (cur = 1)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (problem_123_pre_z n0 )) (PreH5 : (collatz_safe_123 n0 )) (PreH6 : (collatz_final_count_123 n0 count )) (PreH7 : (cap = (count + 1 ))) (PreH8 : (0 < cur)) (PreH9 : (cur < INT_MAX)) (PreH10 : (0 < count)) (PreH11 : ((count + 1 ) < INT_MAX)) (PreH12 : (1 <= size)) (PreH13 : (size <= count)) (PreH14 : (size = (Zlength (output_l_2)))) (PreH15 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (collatz_output_state_123 n0 count 1 output_l_2 ) ” 
  &&  “ (size = count) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_6_split_goal_1 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (cur = 1)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (problem_123_pre_z n0 )) (PreH5 : (collatz_safe_123 n0 )) (PreH6 : (collatz_final_count_123 n0 count )) (PreH7 : (cap = (count + 1 ))) (PreH8 : (0 < cur)) (PreH9 : (cur < INT_MAX)) (PreH10 : (0 < count)) (PreH11 : ((count + 1 ) < INT_MAX)) (PreH12 : (1 <= size)) (PreH13 : (size <= count)) (PreH14 : (size = (Zlength (output_l_2)))) (PreH15 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (collatz_output_state_123 n0 count 1 output_l_2 ) ”
.

Definition get_odd_collatz_entail_wit_6_split_goal_2 := 
forall (n0: Z) (output_l_2: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : (cur = 1)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (problem_123_pre_z n0 )) (PreH5 : (collatz_safe_123 n0 )) (PreH6 : (collatz_final_count_123 n0 count )) (PreH7 : (cap = (count + 1 ))) (PreH8 : (0 < cur)) (PreH9 : (cur < INT_MAX)) (PreH10 : (0 < count)) (PreH11 : ((count + 1 ) < INT_MAX)) (PreH12 : (1 <= size)) (PreH13 : (size <= count)) (PreH14 : (size = (Zlength (output_l_2)))) (PreH15 : (collatz_output_state_123 n0 count cur output_l_2 )) ,
  TT && emp 
|--
  “ (size = count) ”
.

Definition get_odd_collatz_entail_wit_7 := 
(
forall (n0: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (size = (Zlength (sorted_l_2)))) (PreH2 : (cap = (Zlength (sorted_full_l)))) (PreH3 : (0 <= size)) (PreH4 : (size <= cap)) (PreH5 : (0 <= cap)) (PreH6 : (cap < INT_MAX)) (PreH7 : ((sublist (0) (size) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation output_l_2 sorted_l_2 )) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (problem_123_pre_z n0 )) (PreH13 : (collatz_safe_123 n0 )) (PreH14 : (collatz_final_count_123 n0 count )) (PreH15 : (cap = (count + 1 ))) (PreH16 : (size = count)) (PreH17 : (size = (Zlength (output_l_2)))) (PreH18 : (collatz_output_state_123 n0 count 1 output_l_2 )) ,
  (IntArray.full data cap sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (data_l: (@list Z))  (sorted_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (cap = (count + 1 )) ” 
  &&  “ (size = count) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (size = (Zlength (sorted_l))) ” 
  &&  “ (cap = (Zlength (data_l))) ” 
  &&  “ ((sublist (0) (size) (data_l)) = sorted_l) ” 
  &&  “ (collatz_output_state_123 n0 count 1 output_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation output_l sorted_l ) ” 
  &&  “ (problem_123_spec_z n0 sorted_l ) ”
  &&  (IntArray.full data cap data_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
) \/
(
forall (n0: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (size = (Zlength (sorted_l_2)))) (PreH2 : (cap = (Zlength (sorted_full_l)))) (PreH3 : (0 <= size)) (PreH4 : (size <= cap)) (PreH5 : (0 <= cap)) (PreH6 : (cap < INT_MAX)) (PreH7 : ((sublist (0) (size) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation output_l_2 sorted_l_2 )) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (problem_123_pre_z n0 )) (PreH13 : (collatz_safe_123 n0 )) (PreH14 : (collatz_final_count_123 n0 count )) (PreH15 : (cap = (count + 1 ))) (PreH16 : (size = count)) (PreH17 : (size = (Zlength (output_l_2)))) (PreH18 : (collatz_output_state_123 n0 count 1 output_l_2 )) ,
  TT && emp 
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (cap = (count + 1 )) ” 
  &&  “ (size = count) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (size = (Zlength ((sublist (0) (size) (sorted_full_l))))) ” 
  &&  “ (cap = (Zlength (sorted_full_l))) ” 
  &&  “ (collatz_output_state_123 n0 count 1 output_l ) ” 
  &&  “ (sorted_int_list_by 1 (sublist (0) (size) (sorted_full_l)) ) ” 
  &&  “ (Permutation output_l (sublist (0) (size) (sorted_full_l)) ) ” 
  &&  “ (problem_123_spec_z n0 (sublist (0) (size) (sorted_full_l)) ) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_8 := 
(
forall (n0: Z) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (size = count)) (PreH8 : (size = (Zlength (output_l_2)))) (PreH9 : (size = (Zlength (sorted_l)))) (PreH10 : (cap = (Zlength (data_l_2)))) (PreH11 : ((sublist (0) (size) (data_l_2)) = sorted_l)) (PreH12 : (collatz_output_state_123 n0 count 1 output_l_2 )) (PreH13 : (sorted_int_list_by 1 sorted_l )) (PreH14 : (Permutation output_l_2 sorted_l )) (PreH15 : (problem_123_spec_z n0 sorted_l )) ,
  (IntArray.full data cap data_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
|--
  EX (data_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_spec_z n0 output_l ) ” 
  &&  “ (0 < size) ” 
  &&  “ (size < cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (cap = (Zlength (data_l))) ” 
  &&  “ ((sublist (0) (size) (data_l)) = output_l) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.full data cap data_l )
) \/
(
forall (n0: Z) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (size = count)) (PreH8 : (size = (Zlength (output_l_2)))) (PreH9 : (size = (Zlength (sorted_l)))) (PreH10 : (cap = (Zlength (data_l_2)))) (PreH11 : ((sublist (0) (size) (data_l_2)) = sorted_l)) (PreH12 : (collatz_output_state_123 n0 count 1 output_l_2 )) (PreH13 : (sorted_int_list_by 1 sorted_l )) (PreH14 : (Permutation output_l_2 sorted_l )) (PreH15 : (problem_123_spec_z n0 sorted_l )) ,
  TT && emp 
|--
  “ (cap < INT_MAX) ” 
  &&  “ (0 < size) ”
  &&  emp
).

Definition get_odd_collatz_entail_wit_8_split_goal_1 := 
forall (n0: Z) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (size = count)) (PreH8 : (size = (Zlength (output_l_2)))) (PreH9 : (size = (Zlength (sorted_l)))) (PreH10 : (cap = (Zlength (data_l_2)))) (PreH11 : ((sublist (0) (size) (data_l_2)) = sorted_l)) (PreH12 : (collatz_output_state_123 n0 count 1 output_l_2 )) (PreH13 : (sorted_int_list_by 1 sorted_l )) (PreH14 : (Permutation output_l_2 sorted_l )) (PreH15 : (problem_123_spec_z n0 sorted_l )) ,
  TT && emp 
|--
  “ (cap < INT_MAX) ”
.

Definition get_odd_collatz_entail_wit_8_split_goal_2 := 
forall (n0: Z) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (size = count)) (PreH8 : (size = (Zlength (output_l_2)))) (PreH9 : (size = (Zlength (sorted_l)))) (PreH10 : (cap = (Zlength (data_l_2)))) (PreH11 : ((sublist (0) (size) (data_l_2)) = sorted_l)) (PreH12 : (collatz_output_state_123 n0 count 1 output_l_2 )) (PreH13 : (sorted_int_list_by 1 sorted_l )) (PreH14 : (Permutation output_l_2 sorted_l )) (PreH15 : (problem_123_spec_z n0 sorted_l )) ,
  TT && emp 
|--
  “ (0 < size) ”
.

Definition get_odd_collatz_return_wit_1 := 
(
forall (n0: Z) (output_l_2: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (size: Z) (cap: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (problem_123_spec_z n0 output_l_2 )) (PreH4 : (0 < size)) (PreH5 : (size < cap)) (PreH6 : (cap < INT_MAX)) (PreH7 : (size = (Zlength (output_l_2)))) (PreH8 : (cap = (Zlength (data_l_2)))) (PreH9 : ((sublist (0) (size) (data_l_2)) = output_l_2)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.full data_2 cap data_l_2 )
|--
  EX (data_l: (@list Z))  (output_l: (@list Z))  (data_cap: Z)  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 < output_size) ” 
  &&  “ (output_size < INT_MAX) ” 
  &&  “ (output_size < data_cap) ” 
  &&  “ (data_cap < INT_MAX) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (data_cap = (Zlength (data_l))) ” 
  &&  “ ((sublist (0) (output_size) (data_l)) = output_l) ” 
  &&  “ (problem_123_spec_z n0 output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data data_cap data_l )
) \/
(
forall (n0: Z) (output_l: (@list Z)) (output_l_2: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (size: Z) (cap: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (problem_123_spec_z n0 output_l_2 )) (PreH4 : (0 < size)) (PreH5 : (size < cap)) (PreH6 : (cap < INT_MAX)) (PreH7 : (size = (Zlength (output_l_2)))) (PreH8 : (cap = (Zlength (data_l_2)))) (PreH9 : ((sublist (0) (size) (data_l_2)) = output_l_2)) ,
  (IntArray.full data_2 cap data_l_2 )
|--
  EX (data_l: (@list Z)) ,
  “ (size = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l))))) ” 
  &&  “ (size = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l))))) ” 
  &&  “ (size = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 < (Zlength ((sublist (0) ((Zlength (output_l))) (data_l))))) ” 
  &&  “ ((Zlength ((sublist (0) ((Zlength (output_l))) (data_l)))) < INT_MAX) ” 
  &&  “ ((Zlength ((sublist (0) ((Zlength (output_l))) (data_l)))) < (Zlength (data_l))) ” 
  &&  “ ((Zlength (data_l)) < INT_MAX) ” 
  &&  “ ((sublist (0) ((Zlength ((sublist (0) ((Zlength (output_l))) (data_l))))) (data_l)) = (sublist (0) ((Zlength (output_l))) (data_l))) ” 
  &&  “ (problem_123_spec_z n0 (sublist (0) ((Zlength (output_l))) (data_l)) ) ”
  &&  (IntArray.full data_2 (Zlength (data_l)) data_l )
).

Definition get_odd_collatz_partial_solve_wit_1 := 
forall (n0: Z) (count: Z) (PreH1 : (problem_123_pre_z n0 )) (PreH2 : (collatz_safe_123 n0 )) (PreH3 : (collatz_final_count_123 n0 count )) (PreH4 : (0 < count)) (PreH5 : ((count + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ”
  &&  emp
.

Definition get_odd_collatz_partial_solve_wit_2_pure := 
forall (n0: Z) (count: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (collatz_final_count_123 n0 count )) (PreH5 : (0 < count)) (PreH6 : ((count + 1 ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (count + 1 ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cur" ) )) # Int  |-> n0)
|--
  “ ((count + 1 ) > 0) ” 
  &&  “ ((count + 1 ) < INT_MAX) ”
.

Definition get_odd_collatz_partial_solve_wit_2_aux := 
forall (n0: Z) (count: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (problem_123_pre_z n0 )) (PreH3 : (collatz_safe_123 n0 )) (PreH4 : (collatz_final_count_123 n0 count )) (PreH5 : (0 < count)) (PreH6 : ((count + 1 ) < INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((count + 1 ) > 0) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition get_odd_collatz_partial_solve_wit_2 := get_odd_collatz_partial_solve_wit_2_pure -> get_odd_collatz_partial_solve_wit_2_aux.

Definition get_odd_collatz_partial_solve_wit_3 := 
forall (n0: Z) (count: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (0 < count)) (PreH7 : ((count + 1 ) < INT_MAX)) ,
  (IntArray.undef_full retval_2 (count + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 (count + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition get_odd_collatz_partial_solve_wit_4 := 
forall (n0: Z) (output_l: (@list Z)) (size: Z) (cur: Z) (cap: Z) (count: Z) (data: Z) (out: Z) (PreH1 : ((cur % ( 2 ) ) = 1)) (PreH2 : (cur <> 1)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (problem_123_pre_z n0 )) (PreH6 : (collatz_safe_123 n0 )) (PreH7 : (collatz_final_count_123 n0 count )) (PreH8 : (cap = (count + 1 ))) (PreH9 : (0 < cur)) (PreH10 : (cur < INT_MAX)) (PreH11 : (0 < count)) (PreH12 : ((count + 1 ) < INT_MAX)) (PreH13 : (1 <= size)) (PreH14 : (size <= count)) (PreH15 : (size = (Zlength (output_l)))) (PreH16 : (collatz_output_state_123 n0 count cur output_l )) ,
  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((cur % ( 2 ) ) = 1) ” 
  &&  “ (cur <> 1) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (cap = (count + 1 )) ” 
  &&  “ (0 < cur) ” 
  &&  “ (cur < INT_MAX) ” 
  &&  “ (0 < count) ” 
  &&  “ ((count + 1 ) < INT_MAX) ” 
  &&  “ (1 <= size) ” 
  &&  “ (size <= count) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (collatz_output_state_123 n0 count cur output_l ) ”
  &&  (((data + (size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (size + 1 ) cap )
  **  (IntArray.seg data 0 size output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition get_odd_collatz_partial_solve_wit_5_pure := 
(
forall (n0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (size = count)) (PreH8 : (size = (Zlength (output_l)))) (PreH9 : (collatz_output_state_123 n0 count 1 output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (data <> 0) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (size <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (0 <= size) ”
) \/
(
forall (n0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (n0 <= INT_MAX)) (PreH6 : (1 >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (n0 >= INT_MIN)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (problem_123_pre_z n0 )) (PreH14 : (collatz_safe_123 n0 )) (PreH15 : (collatz_final_count_123 n0 count )) (PreH16 : (cap = (count + 1 ))) (PreH17 : (size = count)) (PreH18 : (size = (Zlength (output_l)))) (PreH19 : (collatz_output_state_123 n0 count 1 output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= size) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ”
).

Definition get_odd_collatz_partial_solve_wit_5_pure_split_goal_1 := 
forall (n0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (n0 <= INT_MAX)) (PreH6 : (1 >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (n0 >= INT_MIN)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (problem_123_pre_z n0 )) (PreH14 : (collatz_safe_123 n0 )) (PreH15 : (collatz_final_count_123 n0 count )) (PreH16 : (cap = (count + 1 ))) (PreH17 : (size = count)) (PreH18 : (size = (Zlength (output_l)))) (PreH19 : (collatz_output_state_123 n0 count 1 output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= size) ”
.

Definition get_odd_collatz_partial_solve_wit_5_pure_split_goal_2 := 
forall (n0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (n0 <= INT_MAX)) (PreH6 : (1 >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (n0 >= INT_MIN)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (problem_123_pre_z n0 )) (PreH14 : (collatz_safe_123 n0 )) (PreH15 : (collatz_final_count_123 n0 count )) (PreH16 : (cap = (count + 1 ))) (PreH17 : (size = count)) (PreH18 : (size = (Zlength (output_l)))) (PreH19 : (collatz_output_state_123 n0 count 1 output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= cap) ”
.

Definition get_odd_collatz_partial_solve_wit_5_pure_split_goal_3 := 
forall (n0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (n0 <= INT_MAX)) (PreH6 : (1 >= INT_MIN)) (PreH7 : (size >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (n0 >= INT_MIN)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (problem_123_pre_z n0 )) (PreH14 : (collatz_safe_123 n0 )) (PreH15 : (collatz_final_count_123 n0 count )) (PreH16 : (cap = (count + 1 ))) (PreH17 : (size = count)) (PreH18 : (size = (Zlength (output_l)))) (PreH19 : (collatz_output_state_123 n0 count 1 output_l )) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (cap < INT_MAX) ”
.

Definition get_odd_collatz_partial_solve_wit_5_aux := 
forall (n0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (count: Z) (cap: Z) (size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (problem_123_pre_z n0 )) (PreH4 : (collatz_safe_123 n0 )) (PreH5 : (collatz_final_count_123 n0 count )) (PreH6 : (cap = (count + 1 ))) (PreH7 : (size = count)) (PreH8 : (size = (Zlength (output_l)))) (PreH9 : (collatz_output_state_123 n0 count 1 output_l )) ,
  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (data <> 0) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (size <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (0 <= size) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_123_pre_z n0 ) ” 
  &&  “ (collatz_safe_123 n0 ) ” 
  &&  “ (collatz_final_count_123 n0 count ) ” 
  &&  “ (cap = (count + 1 )) ” 
  &&  “ (size = count) ” 
  &&  “ (size = (Zlength (output_l))) ” 
  &&  “ (collatz_output_state_123 n0 count 1 output_l ) ”
  &&  (IntArray.seg data 0 size output_l )
  **  (IntArray.undef_seg data size cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition get_odd_collatz_partial_solve_wit_5 := get_odd_collatz_partial_solve_wit_5_pure -> get_odd_collatz_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_get_odd_collatz_safety_wit_1 : get_odd_collatz_safety_wit_1.
Axiom proof_of_get_odd_collatz_safety_wit_2 : get_odd_collatz_safety_wit_2.
Axiom proof_of_get_odd_collatz_safety_wit_3 : get_odd_collatz_safety_wit_3.
Axiom proof_of_get_odd_collatz_safety_wit_4 : get_odd_collatz_safety_wit_4.
Axiom proof_of_get_odd_collatz_safety_wit_5 : get_odd_collatz_safety_wit_5.
Axiom proof_of_get_odd_collatz_safety_wit_6 : get_odd_collatz_safety_wit_6.
Axiom proof_of_get_odd_collatz_safety_wit_7 : get_odd_collatz_safety_wit_7.
Axiom proof_of_get_odd_collatz_safety_wit_8 : get_odd_collatz_safety_wit_8.
Axiom proof_of_get_odd_collatz_safety_wit_9 : get_odd_collatz_safety_wit_9.
Axiom proof_of_get_odd_collatz_safety_wit_10 : get_odd_collatz_safety_wit_10.
Axiom proof_of_get_odd_collatz_safety_wit_11 : get_odd_collatz_safety_wit_11.
Axiom proof_of_get_odd_collatz_safety_wit_12 : get_odd_collatz_safety_wit_12.
Axiom proof_of_get_odd_collatz_safety_wit_13 : get_odd_collatz_safety_wit_13.
Axiom proof_of_get_odd_collatz_safety_wit_14 : get_odd_collatz_safety_wit_14.
Axiom proof_of_get_odd_collatz_safety_wit_15 : get_odd_collatz_safety_wit_15.
Axiom proof_of_get_odd_collatz_safety_wit_16 : get_odd_collatz_safety_wit_16.
Axiom proof_of_get_odd_collatz_safety_wit_17 : get_odd_collatz_safety_wit_17.
Axiom proof_of_get_odd_collatz_safety_wit_18 : get_odd_collatz_safety_wit_18.
Axiom proof_of_get_odd_collatz_safety_wit_19 : get_odd_collatz_safety_wit_19.
Axiom proof_of_get_odd_collatz_safety_wit_20 : get_odd_collatz_safety_wit_20.
Axiom proof_of_get_odd_collatz_safety_wit_21 : get_odd_collatz_safety_wit_21.
Axiom proof_of_get_odd_collatz_safety_wit_22 : get_odd_collatz_safety_wit_22.
Axiom proof_of_get_odd_collatz_safety_wit_23 : get_odd_collatz_safety_wit_23.
Axiom proof_of_get_odd_collatz_safety_wit_24 : get_odd_collatz_safety_wit_24.
Axiom proof_of_get_odd_collatz_safety_wit_25 : get_odd_collatz_safety_wit_25.
Axiom proof_of_get_odd_collatz_safety_wit_26 : get_odd_collatz_safety_wit_26.
Axiom proof_of_get_odd_collatz_safety_wit_27 : get_odd_collatz_safety_wit_27.
Axiom proof_of_get_odd_collatz_safety_wit_28 : get_odd_collatz_safety_wit_28.
Axiom proof_of_get_odd_collatz_safety_wit_29 : get_odd_collatz_safety_wit_29.
Axiom proof_of_get_odd_collatz_safety_wit_30 : get_odd_collatz_safety_wit_30.
Axiom proof_of_get_odd_collatz_safety_wit_31 : get_odd_collatz_safety_wit_31.
Axiom proof_of_get_odd_collatz_entail_wit_1 : get_odd_collatz_entail_wit_1.
Axiom proof_of_get_odd_collatz_entail_wit_2_1 : get_odd_collatz_entail_wit_2_1.
Axiom proof_of_get_odd_collatz_entail_wit_2_2 : get_odd_collatz_entail_wit_2_2.
Axiom proof_of_get_odd_collatz_entail_wit_3 : get_odd_collatz_entail_wit_3.
Axiom proof_of_get_odd_collatz_entail_wit_4 : get_odd_collatz_entail_wit_4.
Axiom proof_of_get_odd_collatz_entail_wit_5_1 : get_odd_collatz_entail_wit_5_1.
Axiom proof_of_get_odd_collatz_entail_wit_5_2 : get_odd_collatz_entail_wit_5_2.
Axiom proof_of_get_odd_collatz_entail_wit_6 : get_odd_collatz_entail_wit_6.
Axiom proof_of_get_odd_collatz_entail_wit_7 : get_odd_collatz_entail_wit_7.
Axiom proof_of_get_odd_collatz_entail_wit_8 : get_odd_collatz_entail_wit_8.
Axiom proof_of_get_odd_collatz_return_wit_1 : get_odd_collatz_return_wit_1.
Axiom proof_of_get_odd_collatz_partial_solve_wit_1 : get_odd_collatz_partial_solve_wit_1.
Axiom proof_of_get_odd_collatz_partial_solve_wit_2_pure : get_odd_collatz_partial_solve_wit_2_pure.
Axiom proof_of_get_odd_collatz_partial_solve_wit_2 : get_odd_collatz_partial_solve_wit_2.
Axiom proof_of_get_odd_collatz_partial_solve_wit_3 : get_odd_collatz_partial_solve_wit_3.
Axiom proof_of_get_odd_collatz_partial_solve_wit_4 : get_odd_collatz_partial_solve_wit_4.
Axiom proof_of_get_odd_collatz_partial_solve_wit_5_pure : get_odd_collatz_partial_solve_wit_5_pure.
Axiom proof_of_get_odd_collatz_partial_solve_wit_5 : get_odd_collatz_partial_solve_wit_5.

End VC_Correct.
