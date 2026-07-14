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
Require Import coins_155.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function even_odd_count -----*)

Definition even_odd_count_safety_wit_1 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = num0)) (PreH2 : (INT_MIN < num0)) (PreH3 : (num0 <= INT_MAX)) (PreH4 : (problem_155_pre_z num0 )) (PreH5 : (even_odd_safe_155 num0 )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_2 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre < 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (num_pre <> (INT_MIN)) ”
.

Definition even_odd_count_safety_wit_3 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre < 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "n2" ) )) # Int  |->_)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> (-num_pre))
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_4 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre >= 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "n2" ) )) # Int  |->_)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_5 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre < 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int  |-> (-num_pre))
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_6 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre >= 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int  |-> num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_7 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre < 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> (-num_pre))
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_8 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre >= 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_9 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre < 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> (-num_pre))
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_10 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre >= 0)) (PreH2 : (num_pre = num0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_11 := 
forall (num_pre: Z) (num0: Z) (PreH1 : ((-num_pre) = 0)) (PreH2 : (num_pre < 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> (-num_pre))
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ False ”
.

Definition even_odd_count_safety_wit_12 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "n2" ) )) # Int  |-> 0)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_count_safety_wit_13 := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (INT_MIN < num0)) (PreH2 : (num0 <= INT_MAX)) (PreH3 : (problem_155_pre_z num0 )) (PreH4 : (even_odd_safe_155 num0 )) (PreH5 : (0 <= w)) (PreH6 : (w <= (Zabs_155 (num0)))) (PreH7 : (0 <= n1)) (PreH8 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH9 : (0 <= n2)) (PreH10 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_14 := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (w > 0)) (PreH2 : (INT_MIN < num0)) (PreH3 : (num0 <= INT_MAX)) (PreH4 : (problem_155_pre_z num0 )) (PreH5 : (even_odd_safe_155 num0 )) (PreH6 : (0 <= w)) (PreH7 : (w <= (Zabs_155 (num0)))) (PreH8 : (0 <= n1)) (PreH9 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH10 : (0 <= n2)) (PreH11 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ ((w <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition even_odd_count_safety_wit_15 := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (w > 0)) (PreH2 : (INT_MIN < num0)) (PreH3 : (num0 <= INT_MAX)) (PreH4 : (problem_155_pre_z num0 )) (PreH5 : (even_odd_safe_155 num0 )) (PreH6 : (0 <= w)) (PreH7 : (w <= (Zabs_155 (num0)))) (PreH8 : (0 <= n1)) (PreH9 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH10 : (0 <= n2)) (PreH11 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition even_odd_count_safety_wit_16 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (w > 0)) (PreH2 : (INT_MIN < num0)) (PreH3 : (num0 <= INT_MAX)) (PreH4 : (problem_155_pre_z num0 )) (PreH5 : (even_odd_safe_155 num0 )) (PreH6 : (0 <= w)) (PreH7 : (w <= (Zabs_155 (num0)))) (PreH8 : (0 <= n1)) (PreH9 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH10 : (0 <= n2)) (PreH11 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ (((w % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition even_odd_count_safety_wit_17 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (w > 0)) (PreH2 : (INT_MIN < num0)) (PreH3 : (num0 <= INT_MAX)) (PreH4 : (problem_155_pre_z num0 )) (PreH5 : (even_odd_safe_155 num0 )) (PreH6 : (0 <= w)) (PreH7 : (w <= (Zabs_155 (num0)))) (PreH8 : (0 <= n1)) (PreH9 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH10 : (0 <= n2)) (PreH11 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_count_safety_wit_18 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (w > 0)) (PreH2 : (INT_MIN < num0)) (PreH3 : (num0 <= INT_MAX)) (PreH4 : (problem_155_pre_z num0 )) (PreH5 : (even_odd_safe_155 num0 )) (PreH6 : (0 <= w)) (PreH7 : (w <= (Zabs_155 (num0)))) (PreH8 : (0 <= n1)) (PreH9 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH10 : (0 <= n2)) (PreH11 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_count_safety_wit_19 := 
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((n1 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n1 + 1 )) ”
) \/
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((n1 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n1 + 1 )) ”
).

Definition even_odd_count_safety_wit_19_split_goal_1 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((n1 + 1 ) <= INT_MAX) ”
.

Definition even_odd_count_safety_wit_19_split_goal_2 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((INT_MIN) <= (n1 + 1 )) ”
.

Definition even_odd_count_safety_wit_20 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_count_safety_wit_21 := 
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((n2 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n2 + 1 )) ”
) \/
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((n2 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n2 + 1 )) ”
).

Definition even_odd_count_safety_wit_21_split_goal_1 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((n2 + 1 ) <= INT_MAX) ”
.

Definition even_odd_count_safety_wit_21_split_goal_2 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((INT_MIN) <= (n2 + 1 )) ”
.

Definition even_odd_count_safety_wit_22 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_count_safety_wit_23 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> (n1 + 1 ))
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((w <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition even_odd_count_safety_wit_24 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> (n1 + 1 ))
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition even_odd_count_safety_wit_25 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> (n2 + 1 ))
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ ((w <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition even_odd_count_safety_wit_26 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> (n2 + 1 ))
  **  ((( &( "d" ) )) # Int  |-> (w % ( 10 ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition even_odd_count_safety_wit_27 := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (w <= 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_count_safety_wit_28 := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (w <= 0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) (PreH8 : (0 <= w)) (PreH9 : (w <= (Zabs_155 (num0)))) (PreH10 : (0 <= n1)) (PreH11 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (0 <= n2)) (PreH13 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH14 : (digit_count_state_155 num0 w n2 n1 )) ,
  (IntArray.undef_full retval_2 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition even_odd_count_safety_wit_29 := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (w <= 0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) (PreH8 : (0 <= w)) (PreH9 : (w <= (Zabs_155 (num0)))) (PreH10 : (0 <= n1)) (PreH11 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (0 <= n2)) (PreH13 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH14 : (digit_count_state_155 num0 w n2 n1 )) ,
  (IntArray.undef_full retval_2 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition even_odd_count_safety_wit_30 := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (w <= 0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) (PreH8 : (0 <= w)) (PreH9 : (w <= (Zabs_155 (num0)))) (PreH10 : (0 <= n1)) (PreH11 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (0 <= n2)) (PreH13 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH14 : (digit_count_state_155 num0 w n2 n1 )) ,
  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition even_odd_count_entail_wit_1_1 := 
(
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 num_pre 1 0 ) ”
  &&  ((( &( "num" ) )) # Int  |-> num0)
) \/
(
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 num_pre 1 0 ) ” 
  &&  “ (1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (num_pre <= (Zabs_155 (num0))) ”
  &&  emp
).

Definition even_odd_count_entail_wit_1_1_split_goal_1 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 num_pre 1 0 ) ”
.

Definition even_odd_count_entail_wit_1_1_split_goal_2 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (1 <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_1_1_split_goal_3 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (0 <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_1_1_split_goal_4 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre = 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (num_pre <= (Zabs_155 (num0))) ”
.

Definition even_odd_count_entail_wit_1_2 := 
(
forall (num_pre: Z) (num0: Z) (PreH1 : ((-num_pre) <> 0)) (PreH2 : (num_pre < 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= (-num_pre)) ” 
  &&  “ ((-num_pre) <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 (-num_pre) 0 0 ) ”
  &&  ((( &( "num" ) )) # Int  |-> num0)
) \/
(
forall (num_pre: Z) (num0: Z) (PreH1 : ((-num_pre) <> 0)) (PreH2 : (num_pre < 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 (-num_pre) 0 0 ) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ ((-num_pre) <= (Zabs_155 (num0))) ”
  &&  emp
).

Definition even_odd_count_entail_wit_1_2_split_goal_1 := 
forall (num_pre: Z) (num0: Z) (PreH1 : ((-num_pre) <> 0)) (PreH2 : (num_pre < 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 (-num_pre) 0 0 ) ”
.

Definition even_odd_count_entail_wit_1_2_split_goal_2 := 
forall (num_pre: Z) (num0: Z) (PreH1 : ((-num_pre) <> 0)) (PreH2 : (num_pre < 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (0 <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_1_2_split_goal_3 := 
forall (num_pre: Z) (num0: Z) (PreH1 : ((-num_pre) <> 0)) (PreH2 : (num_pre < 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (0 <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_1_2_split_goal_4 := 
forall (num_pre: Z) (num0: Z) (PreH1 : ((-num_pre) <> 0)) (PreH2 : (num_pre < 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ ((-num_pre) <= (Zabs_155 (num0))) ”
.

Definition even_odd_count_entail_wit_1_3 := 
(
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 num_pre 0 0 ) ”
  &&  ((( &( "num" ) )) # Int  |-> num0)
) \/
(
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 num_pre 0 0 ) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (num_pre <= (Zabs_155 (num0))) ”
  &&  emp
).

Definition even_odd_count_entail_wit_1_3_split_goal_1 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 num_pre 0 0 ) ”
.

Definition even_odd_count_entail_wit_1_3_split_goal_2 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (0 <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_1_3_split_goal_3 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (0 <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_1_3_split_goal_4 := 
forall (num_pre: Z) (num0: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (num_pre >= 0)) (PreH3 : (num_pre = num0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) ,
  TT && emp 
|--
  “ (num_pre <= (Zabs_155 (num0))) ”
.

Definition even_odd_count_entail_wit_2_1 := 
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= (w ÷ 10 )) ” 
  &&  “ ((w ÷ 10 ) <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= (n2 + 1 )) ” 
  &&  “ ((n2 + 1 ) <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 (w ÷ 10 ) (n2 + 1 ) n1 ) ”
  &&  emp
) \/
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 (w ÷ 10 ) (n2 + 1 ) n1 ) ” 
  &&  “ ((n2 + 1 ) <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ ((w ÷ 10 ) <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= (w ÷ 10 )) ”
  &&  emp
).

Definition even_odd_count_entail_wit_2_1_split_goal_1 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 (w ÷ 10 ) (n2 + 1 ) n1 ) ”
.

Definition even_odd_count_entail_wit_2_1_split_goal_2 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ ((n2 + 1 ) <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_2_1_split_goal_3 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ ((w ÷ 10 ) <= (Zabs_155 (num0))) ”
.

Definition even_odd_count_entail_wit_2_1_split_goal_4 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (0 <= (w ÷ 10 )) ”
.

Definition even_odd_count_entail_wit_2_2 := 
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= (w ÷ 10 )) ” 
  &&  “ ((w ÷ 10 ) <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ ((n1 + 1 ) <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 (w ÷ 10 ) n2 (n1 + 1 ) ) ”
  &&  emp
) \/
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 (w ÷ 10 ) n2 (n1 + 1 ) ) ” 
  &&  “ ((n1 + 1 ) <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ ((w ÷ 10 ) <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= (w ÷ 10 )) ”
  &&  emp
).

Definition even_odd_count_entail_wit_2_2_split_goal_1 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (digit_count_state_155 num0 (w ÷ 10 ) n2 (n1 + 1 ) ) ”
.

Definition even_odd_count_entail_wit_2_2_split_goal_2 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ ((n1 + 1 ) <= ((Zabs_155 (num0)) + 1 )) ”
.

Definition even_odd_count_entail_wit_2_2_split_goal_3 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ ((w ÷ 10 ) <= (Zabs_155 (num0))) ”
.

Definition even_odd_count_entail_wit_2_2_split_goal_4 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (((w % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (w > 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (0 <= (w ÷ 10 )) ”
.

Definition even_odd_count_entail_wit_3 := 
forall (num0: Z) (w: Z) (n1: Z) (n2: Z) (PreH1 : (INT_MIN < num0)) (PreH2 : (num0 <= INT_MAX)) (PreH3 : (problem_155_pre_z num0 )) (PreH4 : (even_odd_safe_155 num0 )) (PreH5 : (0 <= w)) (PreH6 : (w <= (Zabs_155 (num0)))) (PreH7 : (0 <= n1)) (PreH8 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH9 : (0 <= n2)) (PreH10 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 w n2 n1 ) ”
  &&  emp
.

Definition even_odd_count_entail_wit_4 := 
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (w <= 0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) (PreH8 : (0 <= w)) (PreH9 : (w <= (Zabs_155 (num0)))) (PreH10 : (0 <= n1)) (PreH11 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (0 <= n2)) (PreH13 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH14 : (digit_count_state_155 num0 w n2 n1 )) ,
  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> n1)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "w" ) )) # Int  |-> w)
|--
  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (digit_count_state_155 num0 0 n2 n1 ) ” 
  &&  “ (problem_155_spec_z num0 (cons (n2) ((cons (n1) ((@nil Z))))) ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  ((( &( "w" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full retval_2 2 (cons (n2) ((cons (n1) ((@nil Z))))) )
) \/
(
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (n2 <= INT_MAX)) (PreH2 : (n1 <= INT_MAX)) (PreH3 : (n2 >= INT_MIN)) (PreH4 : (n1 >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (w <= 0)) (PreH8 : (INT_MIN < num0)) (PreH9 : (num0 <= INT_MAX)) (PreH10 : (problem_155_pre_z num0 )) (PreH11 : (even_odd_safe_155 num0 )) (PreH12 : (0 <= w)) (PreH13 : (w <= (Zabs_155 (num0)))) (PreH14 : (0 <= n1)) (PreH15 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH16 : (0 <= n2)) (PreH17 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH18 : (digit_count_state_155 num0 w n2 n1 )) ,
  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> n1)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
|--
  “ (problem_155_spec_z num0 (cons (n2) ((cons (n1) ((@nil Z))))) ) ” 
  &&  “ (digit_count_state_155 num0 0 n2 n1 ) ”
  &&  (IntArray.full retval_2 2 (cons (n2) ((cons (n1) ((@nil Z))))) )
).

Definition even_odd_count_entail_wit_4_split_goal_1 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (n2 <= INT_MAX)) (PreH2 : (n1 <= INT_MAX)) (PreH3 : (n2 >= INT_MIN)) (PreH4 : (n1 >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (w <= 0)) (PreH8 : (INT_MIN < num0)) (PreH9 : (num0 <= INT_MAX)) (PreH10 : (problem_155_pre_z num0 )) (PreH11 : (even_odd_safe_155 num0 )) (PreH12 : (0 <= w)) (PreH13 : (w <= (Zabs_155 (num0)))) (PreH14 : (0 <= n1)) (PreH15 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH16 : (0 <= n2)) (PreH17 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH18 : (digit_count_state_155 num0 w n2 n1 )) ,
  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> n1)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
|--
  “ (problem_155_spec_z num0 (cons (n2) ((cons (n1) ((@nil Z))))) ) ”
.

Definition even_odd_count_entail_wit_4_split_goal_2 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (n2 <= INT_MAX)) (PreH2 : (n1 <= INT_MAX)) (PreH3 : (n2 >= INT_MIN)) (PreH4 : (n1 >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (w <= 0)) (PreH8 : (INT_MIN < num0)) (PreH9 : (num0 <= INT_MAX)) (PreH10 : (problem_155_pre_z num0 )) (PreH11 : (even_odd_safe_155 num0 )) (PreH12 : (0 <= w)) (PreH13 : (w <= (Zabs_155 (num0)))) (PreH14 : (0 <= n1)) (PreH15 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH16 : (0 <= n2)) (PreH17 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH18 : (digit_count_state_155 num0 w n2 n1 )) ,
  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> n1)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
|--
  “ (digit_count_state_155 num0 0 n2 n1 ) ”
.

Definition even_odd_count_entail_wit_4_split_goal_spatial := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (n2 <= INT_MAX)) (PreH2 : (n1 <= INT_MAX)) (PreH3 : (n2 >= INT_MIN)) (PreH4 : (n1 >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (w <= 0)) (PreH8 : (INT_MIN < num0)) (PreH9 : (num0 <= INT_MAX)) (PreH10 : (problem_155_pre_z num0 )) (PreH11 : (even_odd_safe_155 num0 )) (PreH12 : (0 <= w)) (PreH13 : (w <= (Zabs_155 (num0)))) (PreH14 : (0 <= n1)) (PreH15 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH16 : (0 <= n2)) (PreH17 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH18 : (digit_count_state_155 num0 w n2 n1 )) ,
  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> n1)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
|--
  (IntArray.full retval_2 2 (cons (n2) ((cons (n1) ((@nil Z))))) )
.

Definition even_odd_count_return_wit_1 := 
forall (num0: Z) (n1: Z) (n2: Z) (out: Z) (data_2: Z) (PreH1 : (problem_155_pre_z num0 )) (PreH2 : (even_odd_safe_155 num0 )) (PreH3 : (digit_count_state_155 num0 0 n2 n1 )) (PreH4 : (problem_155_spec_z num0 (cons (n2) ((cons (n1) ((@nil Z))))) )) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data_2 2 (cons (n2) ((cons (n1) ((@nil Z))))) )
|--
  EX (even: Z)  (odd: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_155_spec_z num0 (cons (even) ((cons (odd) ((@nil Z))))) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 (cons (even) ((cons (odd) ((@nil Z))))) )
.

Definition even_odd_count_partial_solve_wit_1 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (PreH1 : (w <= 0)) (PreH2 : (INT_MIN < num0)) (PreH3 : (num0 <= INT_MAX)) (PreH4 : (problem_155_pre_z num0 )) (PreH5 : (even_odd_safe_155 num0 )) (PreH6 : (0 <= w)) (PreH7 : (w <= (Zabs_155 (num0)))) (PreH8 : (0 <= n1)) (PreH9 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH10 : (0 <= n2)) (PreH11 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (digit_count_state_155 num0 w n2 n1 )) ,
  TT && emp 
|--
  “ (w <= 0) ” 
  &&  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 w n2 n1 ) ”
  &&  emp
.

Definition even_odd_count_partial_solve_wit_2_pure := 
forall (num0: Z) (d_addr_v: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (w <= 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num0)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "d" ) )) # Int  |-> d_addr_v)
|--
  “ (2 > 0) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition even_odd_count_partial_solve_wit_2_aux := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (w <= 0)) (PreH3 : (INT_MIN < num0)) (PreH4 : (num0 <= INT_MAX)) (PreH5 : (problem_155_pre_z num0 )) (PreH6 : (even_odd_safe_155 num0 )) (PreH7 : (0 <= w)) (PreH8 : (w <= (Zabs_155 (num0)))) (PreH9 : (0 <= n1)) (PreH10 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH11 : (0 <= n2)) (PreH12 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH13 : (digit_count_state_155 num0 w n2 n1 )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 > 0) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (w <= 0) ” 
  &&  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 w n2 n1 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition even_odd_count_partial_solve_wit_2 := even_odd_count_partial_solve_wit_2_pure -> even_odd_count_partial_solve_wit_2_aux.

Definition even_odd_count_partial_solve_wit_3 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (w <= 0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) (PreH8 : (0 <= w)) (PreH9 : (w <= (Zabs_155 (num0)))) (PreH10 : (0 <= n1)) (PreH11 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (0 <= n2)) (PreH13 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH14 : (digit_count_state_155 num0 w n2 n1 )) ,
  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (w <= 0) ” 
  &&  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 w n2 n1 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition even_odd_count_partial_solve_wit_4 := 
forall (num0: Z) (n2: Z) (n1: Z) (w: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (w <= 0)) (PreH4 : (INT_MIN < num0)) (PreH5 : (num0 <= INT_MAX)) (PreH6 : (problem_155_pre_z num0 )) (PreH7 : (even_odd_safe_155 num0 )) (PreH8 : (0 <= w)) (PreH9 : (w <= (Zabs_155 (num0)))) (PreH10 : (0 <= n1)) (PreH11 : (n1 <= ((Zabs_155 (num0)) + 1 ))) (PreH12 : (0 <= n2)) (PreH13 : (n2 <= ((Zabs_155 (num0)) + 1 ))) (PreH14 : (digit_count_state_155 num0 w n2 n1 )) ,
  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> n2)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (w <= 0) ” 
  &&  “ (INT_MIN < num0) ” 
  &&  “ (num0 <= INT_MAX) ” 
  &&  “ (problem_155_pre_z num0 ) ” 
  &&  “ (even_odd_safe_155 num0 ) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= (Zabs_155 (num0))) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 <= ((Zabs_155 (num0)) + 1 )) ” 
  &&  “ (digit_count_state_155 num0 w n2 n1 ) ”
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
Axiom proof_of_even_odd_count_safety_wit_24 : even_odd_count_safety_wit_24.
Axiom proof_of_even_odd_count_safety_wit_25 : even_odd_count_safety_wit_25.
Axiom proof_of_even_odd_count_safety_wit_26 : even_odd_count_safety_wit_26.
Axiom proof_of_even_odd_count_safety_wit_27 : even_odd_count_safety_wit_27.
Axiom proof_of_even_odd_count_safety_wit_28 : even_odd_count_safety_wit_28.
Axiom proof_of_even_odd_count_safety_wit_29 : even_odd_count_safety_wit_29.
Axiom proof_of_even_odd_count_safety_wit_30 : even_odd_count_safety_wit_30.
Axiom proof_of_even_odd_count_entail_wit_1_1 : even_odd_count_entail_wit_1_1.
Axiom proof_of_even_odd_count_entail_wit_1_2 : even_odd_count_entail_wit_1_2.
Axiom proof_of_even_odd_count_entail_wit_1_3 : even_odd_count_entail_wit_1_3.
Axiom proof_of_even_odd_count_entail_wit_2_1 : even_odd_count_entail_wit_2_1.
Axiom proof_of_even_odd_count_entail_wit_2_2 : even_odd_count_entail_wit_2_2.
Axiom proof_of_even_odd_count_entail_wit_3 : even_odd_count_entail_wit_3.
Axiom proof_of_even_odd_count_entail_wit_4 : even_odd_count_entail_wit_4.
Axiom proof_of_even_odd_count_return_wit_1 : even_odd_count_return_wit_1.
Axiom proof_of_even_odd_count_partial_solve_wit_1 : even_odd_count_partial_solve_wit_1.
Axiom proof_of_even_odd_count_partial_solve_wit_2_pure : even_odd_count_partial_solve_wit_2_pure.
Axiom proof_of_even_odd_count_partial_solve_wit_2 : even_odd_count_partial_solve_wit_2.
Axiom proof_of_even_odd_count_partial_solve_wit_3 : even_odd_count_partial_solve_wit_3.
Axiom proof_of_even_odd_count_partial_solve_wit_4 : even_odd_count_partial_solve_wit_4.

End VC_Correct.
