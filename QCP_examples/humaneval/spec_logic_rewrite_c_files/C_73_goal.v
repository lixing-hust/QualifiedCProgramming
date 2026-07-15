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
Require Import coins_73.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function smallest_change -----*)

Definition smallest_change_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) ,
  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition smallest_change_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition smallest_change_safety_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= arr_size_pre)) (PreH8 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (((arr_size_pre - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((arr_size_pre - 1 ) - i )) ”
.

Definition smallest_change_safety_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= arr_size_pre)) (PreH8 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((arr_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (arr_size_pre - 1 )) ”
.

Definition smallest_change_safety_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) (PreH6 : (0 <= i)) (PreH7 : ((2 * i ) <= arr_size_pre)) (PreH8 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition smallest_change_safety_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i < ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ (((arr_size_pre - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((arr_size_pre - 1 ) - i )) ”
.

Definition smallest_change_safety_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i < ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ ((arr_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (arr_size_pre - 1 )) ”
.

Definition smallest_change_safety_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i < ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition smallest_change_safety_wit_9 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ ((out + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out + 1 )) ”
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ ((out + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out + 1 )) ”
).

Definition smallest_change_safety_wit_9_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ ((out + 1 ) <= INT_MAX) ”
.

Definition smallest_change_safety_wit_9_split_goal_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ ((INT_MIN) <= (out + 1 )) ”
.

Definition smallest_change_safety_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition smallest_change_safety_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition smallest_change_safety_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) = (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition smallest_change_entail_wit_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_73_pre_z input_l ) ” 
  &&  “ (smallest_change_int_range input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((2 * 0 ) <= arr_size_pre) ” 
  &&  “ (0 = (count_half_mismatches_upto (0) (input_l))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) ,
  TT && emp 
|--
  “ (0 = (count_half_mismatches_upto (0) (input_l))) ”
  &&  emp
).

Definition smallest_change_entail_wit_1_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_73_pre_z input_l )) (PreH5 : (smallest_change_int_range input_l )) ,
  TT && emp 
|--
  “ (0 = (count_half_mismatches_upto (0) (input_l))) ”
.

Definition smallest_change_entail_wit_2_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_73_pre_z input_l ) ” 
  &&  “ (smallest_change_int_range input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((2 * (i + 1 ) ) <= arr_size_pre) ” 
  &&  “ ((out + 1 ) = (count_half_mismatches_upto ((i + 1 )) (input_l))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  TT && emp 
|--
  “ ((out + 1 ) = (count_half_mismatches_upto ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition smallest_change_entail_wit_2_1_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) <> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  TT && emp 
|--
  “ ((out + 1 ) = (count_half_mismatches_upto ((i + 1 )) (input_l))) ”
.

Definition smallest_change_entail_wit_2_2 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) = (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_73_pre_z input_l ) ” 
  &&  “ (smallest_change_int_range input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((2 * (i + 1 ) ) <= arr_size_pre) ” 
  &&  “ (out = (count_half_mismatches_upto ((i + 1 )) (input_l))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) = (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  TT && emp 
|--
  “ (out = (count_half_mismatches_upto ((i + 1 )) (input_l))) ”
  &&  emp
).

Definition smallest_change_entail_wit_2_2_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : ((Znth i input_l 0) = (Znth ((arr_size_pre - 1 ) - i ) input_l 0))) (PreH2 : (i < ((arr_size_pre - 1 ) - i ))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_73_pre_z input_l )) (PreH7 : (smallest_change_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : ((2 * i ) <= arr_size_pre)) (PreH10 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  TT && emp 
|--
  “ (out = (count_half_mismatches_upto ((i + 1 )) (input_l))) ”
.

Definition smallest_change_return_wit_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i >= ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (problem_73_spec_z input_l out ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i >= ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  TT && emp 
|--
  “ (problem_73_spec_z input_l out ) ”
  &&  emp
).

Definition smallest_change_return_wit_1_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i >= ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  TT && emp 
|--
  “ (problem_73_spec_z input_l out ) ”
.

Definition smallest_change_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i < ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (i < ((arr_size_pre - 1 ) - i )) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_73_pre_z input_l ) ” 
  &&  “ (smallest_change_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size_pre) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (input_l))) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
.

Definition smallest_change_partial_solve_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (i: Z) (PreH1 : (i < ((arr_size_pre - 1 ) - i ))) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_73_pre_z input_l )) (PreH6 : (smallest_change_int_range input_l )) (PreH7 : (0 <= i)) (PreH8 : ((2 * i ) <= arr_size_pre)) (PreH9 : (out = (count_half_mismatches_upto (i) (input_l)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (i < ((arr_size_pre - 1 ) - i )) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_73_pre_z input_l ) ” 
  &&  “ (smallest_change_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size_pre) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (input_l))) ”
  &&  (((arr_pre + (((arr_size_pre - 1 ) - i ) * sizeof(INT) ) )) # Int  |-> (Znth ((arr_size_pre - 1 ) - i ) input_l 0))
  **  (IntArray.missing_i arr_pre ((arr_size_pre - 1 ) - i ) 0 arr_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_smallest_change_safety_wit_1 : smallest_change_safety_wit_1.
Axiom proof_of_smallest_change_safety_wit_2 : smallest_change_safety_wit_2.
Axiom proof_of_smallest_change_safety_wit_3 : smallest_change_safety_wit_3.
Axiom proof_of_smallest_change_safety_wit_4 : smallest_change_safety_wit_4.
Axiom proof_of_smallest_change_safety_wit_5 : smallest_change_safety_wit_5.
Axiom proof_of_smallest_change_safety_wit_6 : smallest_change_safety_wit_6.
Axiom proof_of_smallest_change_safety_wit_7 : smallest_change_safety_wit_7.
Axiom proof_of_smallest_change_safety_wit_8 : smallest_change_safety_wit_8.
Axiom proof_of_smallest_change_safety_wit_9 : smallest_change_safety_wit_9.
Axiom proof_of_smallest_change_safety_wit_10 : smallest_change_safety_wit_10.
Axiom proof_of_smallest_change_safety_wit_11 : smallest_change_safety_wit_11.
Axiom proof_of_smallest_change_safety_wit_12 : smallest_change_safety_wit_12.
Axiom proof_of_smallest_change_entail_wit_1 : smallest_change_entail_wit_1.
Axiom proof_of_smallest_change_entail_wit_2_1 : smallest_change_entail_wit_2_1.
Axiom proof_of_smallest_change_entail_wit_2_2 : smallest_change_entail_wit_2_2.
Axiom proof_of_smallest_change_return_wit_1 : smallest_change_return_wit_1.
Axiom proof_of_smallest_change_partial_solve_wit_1 : smallest_change_partial_solve_wit_1.
Axiom proof_of_smallest_change_partial_solve_wit_2 : smallest_change_partial_solve_wit_2.

End VC_Correct.
