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
Require Import coins_116.
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

(*----- Function sort_array -----*)

Definition sort_array_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_116_pre_z input_l )) (PreH6 : (sort_array_116_int_range input_l )) ,
  ((( &( "bin" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_116_pre_z input_l )) (PreH6 : (sort_array_116_int_range input_l )) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "bin" ) )) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_116_pre_z input_l )) (PreH7 : (sort_array_116_int_range input_l )) ,
  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 arr_size_pre )
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "bin" ) )) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) ,
  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 arr_size_pre )
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "bin" ) )) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ False ”
.

Definition sort_array_safety_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 arr_size_pre )
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "bin" ) )) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (m_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_116_pre_z input_l )) (PreH7 : (sort_array_116_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < arr_size_pre)) (PreH10 : ((i + 1 ) = (Zlength (output_l)))) (PreH11 : (sort_copy_prefix_116 (i + 1 ) input_l output_l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) arr_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_array_safety_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (m_addr_v: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) ,
  (IntArray.undef_full retval arr_size_pre )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (m_addr_v: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) ,
  (IntArray.undef_full retval arr_size_pre )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
|--
  “ False ”
.

Definition sort_array_safety_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (m_addr_v: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) ,
  (IntArray.undef_full retval arr_size_pre )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (i: Z) (m_addr_v: Z) (retval: Z) (PreH1 : (retval = (Zabs ((Znth i input_l 0))))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) ,
  (IntArray.full data arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_13 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : (i = (Zlength (score_l)))) (PreH12 : (sort_score_prefix_116 i input_l score_l )) (PreH13 : (0 <= n)) (PreH14 : (n < INT_MAX)) (PreH15 : (0 <= b)) (PreH16 : (b <= 31)) (PreH17 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_14 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((b + (n % ( 2 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b + (n % ( 2 ) ) )) ”
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((b + (n % ( 2 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b + (n % ( 2 ) ) )) ”
).

Definition sort_array_safety_wit_14_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((b + (n % ( 2 ) ) ) <= INT_MAX) ”
.

Definition sort_array_safety_wit_14_split_goal_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((INT_MIN) <= (b + (n % ( 2 ) ) )) ”
.

Definition sort_array_safety_wit_15 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((n <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition sort_array_safety_wit_16 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sort_array_safety_wit_17 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> (b + (n % ( 2 ) ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((n <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition sort_array_safety_wit_18 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> (b + (n % ( 2 ) ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sort_array_safety_wit_19 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (m_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : ((i + 1 ) = (Zlength (score_l)))) (PreH12 : (sort_score_prefix_116 (i + 1 ) input_l score_l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg bin (i + 1 ) arr_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_array_safety_wit_20 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_array_safety_wit_21 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (arr_size_pre = (Zlength (output_l)))) (PreH13 : (arr_size_pre = (Zlength (score_l)))) (PreH14 : (sort_outer_state_116 i input_l output_l score_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_22 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (j < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= arr_size_pre)) (PreH14 : (arr_size_pre = (Zlength (output_l)))) (PreH15 : (arr_size_pre = (Zlength (score_l)))) (PreH16 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_23 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (j < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= arr_size_pre)) (PreH14 : (arr_size_pre = (Zlength (output_l)))) (PreH15 : (arr_size_pre = (Zlength (score_l)))) (PreH16 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_24 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_25 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_26 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH2 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l)))) (PreH17 : (arr_size_pre = (Zlength (score_l)))) (PreH18 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_27 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH2 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l)))) (PreH17 : (arr_size_pre = (Zlength (score_l)))) (PreH18 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_28 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_29 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_30 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_31 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_32 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_33 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_34 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_35 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_36 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_37 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_38 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_39 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_40 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_41 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sort_array_safety_wit_42 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_43 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_array_safety_wit_44 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sort_array_safety_wit_45 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)))) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sort_array_safety_wit_46 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) >= (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sort_array_safety_wit_47 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (m_addr_v: Z) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) <> (Znth (j - 1 ) score_l 0))) (PreH2 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l)))) (PreH17 : (arr_size_pre = (Zlength (score_l)))) (PreH18 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sort_array_safety_wit_48 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (m_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : (arr_size_pre = (Zlength (output_l)))) (PreH12 : (arr_size_pre = (Zlength (score_l)))) (PreH13 : (sort_outer_state_116 (i + 1 ) input_l output_l score_l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_array_entail_wit_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) ,
  (IntArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  EX (output_l: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (0 = (Zlength (output_l))) ” 
  &&  “ (sort_copy_prefix_116 0 input_l output_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 arr_size_pre )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) ,
  TT && emp 
|--
  “ (sort_copy_prefix_116 0 input_l (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  emp
).

Definition sort_array_entail_wit_1_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) ,
  TT && emp 
|--
  “ (sort_copy_prefix_116 0 input_l (@nil Z) ) ”
.

Definition sort_array_entail_wit_1_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition sort_array_entail_wit_2 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l_2)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l_2 )) ,
  (IntArray.seg data 0 (i + 1 ) (app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (output_l))) ” 
  &&  “ (sort_copy_prefix_116 (i + 1 ) input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) arr_size_pre )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l_2)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l_2 )) ,
  TT && emp 
|--
  “ (sort_copy_prefix_116 (i + 1 ) input_l (app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) ) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition sort_array_entail_wit_2_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l_2)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l_2 )) ,
  TT && emp 
|--
  “ (sort_copy_prefix_116 (i + 1 ) input_l (app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) ) ”
.

Definition sort_array_entail_wit_2_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l_2)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l_2 )) ,
  TT && emp 
|--
  “ ((i + 1 ) = (Zlength ((app (output_l_2) ((cons ((Znth i input_l 0)) ((@nil Z)))))))) ”
.

Definition sort_array_entail_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_116_pre_z input_l )) (PreH7 : (sort_array_116_int_range input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < arr_size_pre)) (PreH10 : ((i + 1 ) = (Zlength (output_l_2)))) (PreH11 : (sort_copy_prefix_116 (i + 1 ) input_l output_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l_2 )
  **  (IntArray.undef_seg data (i + 1 ) arr_size_pre )
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= arr_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (output_l))) ” 
  &&  “ (sort_copy_prefix_116 (i + 1 ) input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) arr_size_pre )
.

Definition sort_array_entail_wit_4 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i arr_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ”
  &&  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l )) ,
  (IntArray.seg data 0 i output_l )
|--
  (IntArray.full data arr_size_pre input_l )
).

Definition sort_array_entail_wit_4_split_goal_spatial := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l )) ,
  (IntArray.seg data 0 i output_l )
|--
  (IntArray.full data arr_size_pre input_l )
.

Definition sort_array_entail_wit_5 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) ,
  (IntArray.undef_full retval arr_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (0 = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 0 input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg retval 0 0 score_l )
  **  (IntArray.undef_seg retval 0 arr_size_pre )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) ,
  TT && emp 
|--
  “ (sort_score_prefix_116 0 input_l (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  emp
).

Definition sort_array_entail_wit_5_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) ,
  TT && emp 
|--
  “ (sort_score_prefix_116 0 input_l (@nil Z) ) ”
.

Definition sort_array_entail_wit_5_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition sort_array_entail_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l_2 )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 i input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
.

Definition sort_array_entail_wit_7 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zabs ((Znth i input_l 0))))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  (IntArray.full data arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l_2 )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (retval = (Zabs ((Znth (i) (input_l) (0))))) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 i input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zabs ((Znth i input_l 0))))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (retval = (Zabs ((Znth (i) (input_l) (0))))) ”
  &&  emp
).

Definition sort_array_entail_wit_7_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zabs ((Znth i input_l 0))))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (retval = (Zabs ((Znth (i) (input_l) (0))))) ”
.

Definition sort_array_entail_wit_8 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (n: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (b = 0)) (PreH5 : (n = (Zabs ((Znth (i) (input_l) (0)))))) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (i = (Zlength (score_l_2)))) (PreH14 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l_2 )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 i input_l score_l ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 31) ” 
  &&  “ (bit_count_state_at_116 i input_l n b ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (n: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (b = 0)) (PreH5 : (n = (Zabs ((Znth (i) (input_l) (0)))))) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (i = (Zlength (score_l_2)))) (PreH14 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (bit_count_state_at_116 i input_l n b ) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= n) ”
  &&  emp
).

Definition sort_array_entail_wit_8_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (n: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (b = 0)) (PreH5 : (n = (Zabs ((Znth (i) (input_l) (0)))))) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (i = (Zlength (score_l_2)))) (PreH14 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (bit_count_state_at_116 i input_l n b ) ”
.

Definition sort_array_entail_wit_8_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (n: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (b = 0)) (PreH5 : (n = (Zabs ((Znth (i) (input_l) (0)))))) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (i = (Zlength (score_l_2)))) (PreH14 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (n < INT_MAX) ”
.

Definition sort_array_entail_wit_8_split_goal_3 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (n: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (b = 0)) (PreH5 : (n = (Zabs ((Znth (i) (input_l) (0)))))) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (i = (Zlength (score_l_2)))) (PreH14 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  TT && emp 
|--
  “ (0 <= n) ”
.

Definition sort_array_entail_wit_9 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l_2 )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 i input_l score_l ) ” 
  &&  “ (0 <= (n ÷ 2 )) ” 
  &&  “ ((n ÷ 2 ) < INT_MAX) ” 
  &&  “ (0 <= (b + (n % ( 2 ) ) )) ” 
  &&  “ ((b + (n % ( 2 ) ) ) <= 31) ” 
  &&  “ (bit_count_state_at_116 i input_l (n ÷ 2 ) (b + (n % ( 2 ) ) ) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ (bit_count_state_at_116 i input_l (n ÷ 2 ) (b + (n % ( 2 ) ) ) ) ” 
  &&  “ ((b + (n % ( 2 ) ) ) <= 31) ” 
  &&  “ (0 <= (b + (n % ( 2 ) ) )) ” 
  &&  “ ((n ÷ 2 ) < INT_MAX) ” 
  &&  “ (0 <= (n ÷ 2 )) ”
  &&  emp
).

Definition sort_array_entail_wit_9_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ (bit_count_state_at_116 i input_l (n ÷ 2 ) (b + (n % ( 2 ) ) ) ) ”
.

Definition sort_array_entail_wit_9_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ ((b + (n % ( 2 ) ) ) <= 31) ”
.

Definition sort_array_entail_wit_9_split_goal_3 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ (0 <= (b + (n % ( 2 ) ) )) ”
.

Definition sort_array_entail_wit_9_split_goal_4 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ ((n ÷ 2 ) < INT_MAX) ”
.

Definition sort_array_entail_wit_9_split_goal_5 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n > 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ (0 <= (n ÷ 2 )) ”
.

Definition sort_array_entail_wit_10 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  (IntArray.seg bin 0 (i + 1 ) (app (score_l_2) ((cons (b) ((@nil Z))))) )
  **  (IntArray.undef_seg bin (i + 1 ) arr_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 (i + 1 ) input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg bin (i + 1 ) arr_size_pre )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ (sort_score_prefix_116 (i + 1 ) input_l (app (score_l_2) ((cons (b) ((@nil Z))))) ) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (score_l_2) ((cons (b) ((@nil Z)))))))) ”
  &&  emp
).

Definition sort_array_entail_wit_10_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ (sort_score_prefix_116 (i + 1 ) input_l (app (score_l_2) ((cons (b) ((@nil Z))))) ) ”
.

Definition sort_array_entail_wit_10_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  TT && emp 
|--
  “ ((i + 1 ) = (Zlength ((app (score_l_2) ((cons (b) ((@nil Z)))))))) ”
.

Definition sort_array_entail_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : ((i + 1 ) = (Zlength (score_l_2)))) (PreH12 : (sort_score_prefix_116 (i + 1 ) input_l score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 (i + 1 ) score_l_2 )
  **  (IntArray.undef_seg bin (i + 1 ) arr_size_pre )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= arr_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 (i + 1 ) input_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 (i + 1 ) score_l )
  **  (IntArray.undef_seg bin (i + 1 ) arr_size_pre )
.

Definition sort_array_entail_wit_12 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l_2 )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_outer_state_116 0 input_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (i = (Zlength (score_l_2)))) (PreH13 : (sort_score_prefix_116 i input_l score_l_2 )) ,
  (IntArray.seg bin 0 i score_l_2 )
|--
  EX (score_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_outer_state_116 0 input_l input_l score_l ) ”
  &&  (IntArray.full bin arr_size_pre score_l )
).

Definition sort_array_entail_wit_13 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (arr_size_pre = (Zlength (output_l_2)))) (PreH13 : (arr_size_pre = (Zlength (score_l_2)))) (PreH14 : (sort_outer_state_116 i input_l output_l_2 score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l_2 )
  **  (IntArray.full bin arr_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i 1 input_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (arr_size_pre = (Zlength (output_l_2)))) (PreH13 : (arr_size_pre = (Zlength (score_l_2)))) (PreH14 : (sort_outer_state_116 i input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i 1 input_l output_l_2 score_l_2 ) ”
  &&  emp
).

Definition sort_array_entail_wit_13_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (arr_size_pre = (Zlength (output_l_2)))) (PreH13 : (arr_size_pre = (Zlength (score_l_2)))) (PreH14 : (sort_outer_state_116 i input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i 1 input_l output_l_2 score_l_2 ) ”
.

Definition sort_array_entail_wit_14 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (j >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= arr_size_pre)) (PreH14 : (arr_size_pre = (Zlength (output_l_2)))) (PreH15 : (arr_size_pre = (Zlength (score_l_2)))) (PreH16 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l_2 )
  **  (IntArray.full bin arr_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_outer_state_116 (i + 1 ) input_l output_l score_l ) ”
  &&  ((( &( "j" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (j >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= arr_size_pre)) (PreH14 : (arr_size_pre = (Zlength (output_l_2)))) (PreH15 : (arr_size_pre = (Zlength (score_l_2)))) (PreH16 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_outer_state_116 (i + 1 ) input_l output_l_2 score_l_2 ) ”
  &&  emp
).

Definition sort_array_entail_wit_14_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (j >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= arr_size_pre)) (PreH14 : (arr_size_pre = (Zlength (output_l_2)))) (PreH15 : (arr_size_pre = (Zlength (score_l_2)))) (PreH16 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_outer_state_116 (i + 1 ) input_l output_l_2 score_l_2 ) ”
.

Definition sort_array_entail_wit_15_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) < (Znth (j - 1 ) score_l_2 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l_2)))) (PreH16 : (arr_size_pre = (Zlength (score_l_2)))) (PreH17 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  (IntArray.full bin arr_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i (j + 1 ) input_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) < (Znth (j - 1 ) score_l_2 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l_2)))) (PreH16 : (arr_size_pre = (Zlength (score_l_2)))) (PreH17 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) ) ” 
  &&  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2))))))) ” 
  &&  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2))))))) ”
  &&  emp
).

Definition sort_array_entail_wit_15_1_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) < (Znth (j - 1 ) score_l_2 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l_2)))) (PreH16 : (arr_size_pre = (Zlength (score_l_2)))) (PreH17 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) ) ”
.

Definition sort_array_entail_wit_15_1_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) < (Znth (j - 1 ) score_l_2 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l_2)))) (PreH16 : (arr_size_pre = (Zlength (score_l_2)))) (PreH17 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2))))))) ”
.

Definition sort_array_entail_wit_15_1_split_goal_3 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) < (Znth (j - 1 ) score_l_2 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l_2)))) (PreH16 : (arr_size_pre = (Zlength (score_l_2)))) (PreH17 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2))))))) ”
.

Definition sort_array_entail_wit_15_2 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) < (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  (IntArray.full bin arr_size_pre (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i (j + 1 ) input_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) < (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) ) ” 
  &&  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2))))))) ” 
  &&  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2))))))) ”
  &&  emp
).

Definition sort_array_entail_wit_15_2_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) < (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l (replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2)))) (replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2)))) ) ”
.

Definition sort_array_entail_wit_15_2_split_goal_2 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) < (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j score_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) score_l_2 0)) (score_l_2))))))) ”
.

Definition sort_array_entail_wit_15_2_split_goal_3 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) < (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (arr_size_pre = (Zlength ((replace_Znth ((j - 1 )) ((Znth j output_l_2 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l_2 0)) (output_l_2))))))) ”
.

Definition sort_array_entail_wit_15_3 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) >= (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  (IntArray.full data arr_size_pre output_l_2 )
  **  (IntArray.full bin arr_size_pre score_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i (j + 1 ) input_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) >= (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l output_l_2 score_l_2 ) ”
  &&  emp
).

Definition sort_array_entail_wit_15_3_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l_2 0) >= (Znth (j - 1 ) output_l_2 0))) (PreH2 : ((Znth j score_l_2 0) = (Znth (j - 1 ) score_l_2 0))) (PreH3 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l_2)))) (PreH18 : (arr_size_pre = (Zlength (score_l_2)))) (PreH19 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l output_l_2 score_l_2 ) ”
.

Definition sort_array_entail_wit_15_4 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) <> (Znth (j - 1 ) score_l_2 0))) (PreH2 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l_2)))) (PreH17 : (arr_size_pre = (Zlength (score_l_2)))) (PreH18 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  (IntArray.full bin arr_size_pre score_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i (j + 1 ) input_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) <> (Znth (j - 1 ) score_l_2 0))) (PreH2 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l_2)))) (PreH17 : (arr_size_pre = (Zlength (score_l_2)))) (PreH18 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l output_l_2 score_l_2 ) ”
  &&  emp
).

Definition sort_array_entail_wit_15_4_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l_2 0) <> (Znth (j - 1 ) score_l_2 0))) (PreH2 : ((Znth j score_l_2 0) >= (Znth (j - 1 ) score_l_2 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l_2)))) (PreH17 : (arr_size_pre = (Zlength (score_l_2)))) (PreH18 : (sort_inner_state_116 i j input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (sort_inner_state_116 i (j + 1 ) input_l output_l_2 score_l_2 ) ”
.

Definition sort_array_entail_wit_16 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (score_l_2: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : (arr_size_pre = (Zlength (output_l_2)))) (PreH12 : (arr_size_pre = (Zlength (score_l_2)))) (PreH13 : (sort_outer_state_116 (i + 1 ) input_l output_l_2 score_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l_2 )
  **  (IntArray.full bin arr_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_outer_state_116 (i + 1 ) input_l output_l score_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
.

Definition sort_array_entail_wit_17 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (arr_size_pre = (Zlength (output_l_2)))) (PreH13 : (arr_size_pre = (Zlength (score_l_2)))) (PreH14 : (sort_outer_state_116 i input_l output_l_2 score_l_2 )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l_2 )
  **  (IntArray.full bin arr_size_pre score_l_2 )
|--
  EX (score_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (problem_116_spec_z input_l output_l ) ”
  &&  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
) \/
(
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (arr_size_pre = (Zlength (output_l_2)))) (PreH13 : (arr_size_pre = (Zlength (score_l_2)))) (PreH14 : (sort_outer_state_116 i input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (problem_116_spec_z input_l output_l_2 ) ”
  &&  emp
).

Definition sort_array_entail_wit_17_split_goal_1 := 
forall (arr_size_pre: Z) (input_l: (@list Z)) (score_l_2: (@list Z)) (output_l_2: (@list Z)) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= arr_size_pre)) (PreH12 : (arr_size_pre = (Zlength (output_l_2)))) (PreH13 : (arr_size_pre = (Zlength (score_l_2)))) (PreH14 : (sort_outer_state_116 i input_l output_l_2 score_l_2 )) ,
  TT && emp 
|--
  “ (problem_116_spec_z input_l output_l_2 ) ”
.

Definition sort_array_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (score_l: (@list Z)) (out: Z) (data_2: Z) (bin: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (arr_size_pre = (Zlength (output_l_2)))) (PreH8 : (arr_size_pre = (Zlength (score_l)))) (PreH9 : (problem_116_spec_z input_l output_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data_2 arr_size_pre output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = arr_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (problem_116_spec_z input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data output_size output_l )
.

Definition sort_array_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= arr_size_pre)) (PreH2 : (arr_size_pre < INT_MAX)) (PreH3 : (arr_size_pre = (Zlength (input_l)))) (PreH4 : (problem_116_pre_z input_l )) (PreH5 : (sort_array_116_int_range input_l )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_2_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_116_pre_z input_l )) (PreH6 : (sort_array_116_int_range input_l )) ,
  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "bin" ) )) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (arr_size_pre >= 0) ” 
  &&  “ (arr_size_pre < INT_MAX) ”
.

Definition sort_array_partial_solve_wit_2_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_116_pre_z input_l )) (PreH6 : (sort_array_116_int_range input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (arr_size_pre >= 0) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_2 := sort_array_partial_solve_wit_2_pure -> sort_array_partial_solve_wit_2_aux.

Definition sort_array_partial_solve_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i arr_size_pre )
|--
  “ (i < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (i = (Zlength (output_l))) ” 
  &&  “ (sort_copy_prefix_116 i input_l output_l ) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i arr_size_pre )
.

Definition sort_array_partial_solve_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (i: Z) (data: Z) (out: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= arr_size_pre)) (PreH11 : (i = (Zlength (output_l)))) (PreH12 : (sort_copy_prefix_116 i input_l output_l )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i arr_size_pre )
|--
  “ (i < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (i = (Zlength (output_l))) ” 
  &&  “ (sort_copy_prefix_116 i input_l output_l ) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.seg data 0 i output_l )
.

Definition sort_array_partial_solve_wit_5_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (m_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_116_pre_z input_l )) (PreH7 : (sort_array_116_int_range input_l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
|--
  “ (arr_size_pre >= 0) ” 
  &&  “ (arr_size_pre < INT_MAX) ”
.

Definition sort_array_partial_solve_wit_5_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre < INT_MAX)) (PreH5 : (arr_size_pre = (Zlength (input_l)))) (PreH6 : (problem_116_pre_z input_l )) (PreH7 : (sort_array_116_int_range input_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
|--
  “ (arr_size_pre >= 0) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_5 := sort_array_partial_solve_wit_5_pure -> sort_array_partial_solve_wit_5_aux.

Definition sort_array_partial_solve_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : (i = (Zlength (score_l)))) (PreH12 : (sort_score_prefix_116 i input_l score_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 i input_l score_l ) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i data i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
.

Definition sort_array_partial_solve_wit_7_pure := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (i: Z) (m_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : (i = (Zlength (score_l)))) (PreH12 : (sort_score_prefix_116 i input_l score_l )) ,
  (IntArray.full data arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (INT_MIN < (Znth i input_l 0)) ”
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (i: Z) (m_addr_v: Z) (PreH1 : (m_addr_v <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((Znth i input_l 0) <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (arr_size_pre <= INT_MAX)) (PreH6 : (m_addr_v >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : ((Znth i input_l 0) >= INT_MIN)) (PreH9 : (b >= INT_MIN)) (PreH10 : (arr_size_pre >= INT_MIN)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (bin <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_116_pre_z input_l )) (PreH18 : (sort_array_116_int_range input_l )) (PreH19 : (0 <= i)) (PreH20 : (i < arr_size_pre)) (PreH21 : (i = (Zlength (score_l)))) (PreH22 : (sort_score_prefix_116 i input_l score_l )) ,
  (IntArray.full data arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (INT_MIN < (Znth i input_l 0)) ”
).

Definition sort_array_partial_solve_wit_7_pure_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (b: Z) (i: Z) (m_addr_v: Z) (PreH1 : (m_addr_v <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((Znth i input_l 0) <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (arr_size_pre <= INT_MAX)) (PreH6 : (m_addr_v >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : ((Znth i input_l 0) >= INT_MIN)) (PreH9 : (b >= INT_MIN)) (PreH10 : (arr_size_pre >= INT_MIN)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (bin <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_116_pre_z input_l )) (PreH18 : (sort_array_116_int_range input_l )) (PreH19 : (0 <= i)) (PreH20 : (i < arr_size_pre)) (PreH21 : (i = (Zlength (score_l)))) (PreH22 : (sort_score_prefix_116 i input_l score_l )) ,
  (IntArray.full data arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "n" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (INT_MIN < (Znth i input_l 0)) ”
.

Definition sort_array_partial_solve_wit_7_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (i: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (problem_116_pre_z input_l )) (PreH8 : (sort_array_116_int_range input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < arr_size_pre)) (PreH11 : (i = (Zlength (score_l)))) (PreH12 : (sort_score_prefix_116 i input_l score_l )) ,
  (IntArray.full data arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (INT_MIN < (Znth i input_l 0)) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 i input_l score_l ) ”
  &&  (IntArray.full data arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
.

Definition sort_array_partial_solve_wit_7 := sort_array_partial_solve_wit_7_pure -> sort_array_partial_solve_wit_7_aux.

Definition sort_array_partial_solve_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (i: Z) (n: Z) (b: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (n <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (i = (Zlength (score_l)))) (PreH13 : (sort_score_prefix_116 i input_l score_l )) (PreH14 : (0 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= b)) (PreH17 : (b <= 31)) (PreH18 : (bit_count_state_at_116 i input_l n b )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
  **  (IntArray.undef_seg bin i arr_size_pre )
|--
  “ (n <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = (Zlength (score_l))) ” 
  &&  “ (sort_score_prefix_116 i input_l score_l ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 31) ” 
  &&  “ (bit_count_state_at_116 i input_l n b ) ”
  &&  (((bin + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg bin (i + 1 ) arr_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre input_l )
  **  (IntArray.seg bin 0 i score_l )
.

Definition sort_array_partial_solve_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (j < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= arr_size_pre)) (PreH14 : (arr_size_pre = (Zlength (output_l)))) (PreH15 : (arr_size_pre = (Zlength (score_l)))) (PreH16 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
|--
  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i bin j 0 arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
.

Definition sort_array_partial_solve_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : (j < arr_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (bin <> 0)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : (arr_size_pre = (Zlength (input_l)))) (PreH8 : (problem_116_pre_z input_l )) (PreH9 : (sort_array_116_int_range input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < arr_size_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= arr_size_pre)) (PreH14 : (arr_size_pre = (Zlength (output_l)))) (PreH15 : (arr_size_pre = (Zlength (score_l)))) (PreH16 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i bin (j - 1 ) 0 arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
.

Definition sort_array_partial_solve_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i bin j 0 arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
.

Definition sort_array_partial_solve_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i bin (j - 1 ) 0 arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
.

Definition sort_array_partial_solve_wit_13 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH2 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l)))) (PreH17 : (arr_size_pre = (Zlength (score_l)))) (PreH18 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.missing_i data j 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_14 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH2 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH3 : (j < arr_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (bin <> 0)) (PreH7 : (0 <= arr_size_pre)) (PreH8 : (arr_size_pre < INT_MAX)) (PreH9 : (arr_size_pre = (Zlength (input_l)))) (PreH10 : (problem_116_pre_z input_l )) (PreH11 : (sort_array_116_int_range input_l )) (PreH12 : (0 <= i)) (PreH13 : (i < arr_size_pre)) (PreH14 : (1 <= j)) (PreH15 : (j <= arr_size_pre)) (PreH16 : (arr_size_pre = (Zlength (output_l)))) (PreH17 : (arr_size_pre = (Zlength (score_l)))) (PreH18 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) output_l 0))
  **  (IntArray.missing_i data (j - 1 ) 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_15 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.missing_i data j 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_16 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth j output_l 0))
  **  (IntArray.missing_i data j 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_17 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) output_l 0))
  **  (IntArray.missing_i data (j - 1 ) 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_18 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data j 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_19 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) output_l 0))
  **  (IntArray.missing_i data (j - 1 ) 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_20 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data j 0 arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_21 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data (j - 1 ) 0 arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_22 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((data + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data (j - 1 ) 0 arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_23 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i bin j 0 arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_24 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + (j * sizeof(INT) ) )) # Int  |-> (Znth j score_l 0))
  **  (IntArray.missing_i bin j 0 arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_25 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i bin (j - 1 ) 0 arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_26 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i bin j 0 arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_27 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) score_l 0))
  **  (IntArray.missing_i bin (j - 1 ) 0 arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_28 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i bin j 0 arr_size_pre score_l )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_29 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0))) (PreH2 : (j < arr_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (bin <> 0)) (PreH6 : (0 <= arr_size_pre)) (PreH7 : (arr_size_pre < INT_MAX)) (PreH8 : (arr_size_pre = (Zlength (input_l)))) (PreH9 : (problem_116_pre_z input_l )) (PreH10 : (sort_array_116_int_range input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < arr_size_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= arr_size_pre)) (PreH15 : (arr_size_pre = (Zlength (output_l)))) (PreH16 : (arr_size_pre = (Zlength (score_l)))) (PreH17 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j score_l 0) < (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i bin (j - 1 ) 0 arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_30 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (score_l: (@list Z)) (output_l: (@list Z)) (j: Z) (i: Z) (bin: Z) (data: Z) (out: Z) (PreH1 : ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0))) (PreH2 : ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0))) (PreH3 : ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0))) (PreH4 : (j < arr_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (bin <> 0)) (PreH8 : (0 <= arr_size_pre)) (PreH9 : (arr_size_pre < INT_MAX)) (PreH10 : (arr_size_pre = (Zlength (input_l)))) (PreH11 : (problem_116_pre_z input_l )) (PreH12 : (sort_array_116_int_range input_l )) (PreH13 : (0 <= i)) (PreH14 : (i < arr_size_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= arr_size_pre)) (PreH17 : (arr_size_pre = (Zlength (output_l)))) (PreH18 : (arr_size_pre = (Zlength (score_l)))) (PreH19 : (sort_inner_state_116 i j input_l output_l score_l )) ,
  (IntArray.full bin arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ ((Znth j output_l 0) < (Znth (j - 1 ) output_l 0)) ” 
  &&  “ ((Znth j score_l 0) = (Znth (j - 1 ) score_l 0)) ” 
  &&  “ ((Znth j score_l 0) >= (Znth (j - 1 ) score_l 0)) ” 
  &&  “ (j < arr_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_116_pre_z input_l ) ” 
  &&  “ (sort_array_116_int_range input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= arr_size_pre) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (sort_inner_state_116 i j input_l output_l score_l ) ”
  &&  (((bin + ((j - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i bin (j - 1 ) 0 arr_size_pre (replace_Znth (j) ((Znth (j - 1 ) score_l 0)) (score_l)) )
  **  (IntArray.full data arr_size_pre (replace_Znth ((j - 1 )) ((Znth j output_l 0)) ((replace_Znth (j) ((Znth (j - 1 ) output_l 0)) (output_l)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition sort_array_partial_solve_wit_31_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (m_addr_v: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (arr_size_pre = (Zlength (output_l)))) (PreH8 : (arr_size_pre = (Zlength (score_l)))) (PreH9 : (problem_116_spec_z input_l output_l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "bin" ) )) # Ptr  |-> bin)
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
|--
  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ”
.

Definition sort_array_partial_solve_wit_31_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (score_l: (@list Z)) (out: Z) (data: Z) (bin: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (bin <> 0)) (PreH4 : (0 <= arr_size_pre)) (PreH5 : (arr_size_pre < INT_MAX)) (PreH6 : (arr_size_pre = (Zlength (input_l)))) (PreH7 : (arr_size_pre = (Zlength (output_l)))) (PreH8 : (arr_size_pre = (Zlength (score_l)))) (PreH9 : (problem_116_spec_z input_l output_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
  **  (IntArray.full bin arr_size_pre score_l )
|--
  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (bin <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (output_l))) ” 
  &&  “ (arr_size_pre = (Zlength (score_l))) ” 
  &&  “ (problem_116_spec_z input_l output_l ) ”
  &&  (IntArray.full bin arr_size_pre score_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data arr_size_pre output_l )
.

Definition sort_array_partial_solve_wit_31 := sort_array_partial_solve_wit_31_pure -> sort_array_partial_solve_wit_31_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_sort_array_safety_wit_1 : sort_array_safety_wit_1.
Axiom proof_of_sort_array_safety_wit_2 : sort_array_safety_wit_2.
Axiom proof_of_sort_array_safety_wit_3 : sort_array_safety_wit_3.
Axiom proof_of_sort_array_safety_wit_4 : sort_array_safety_wit_4.
Axiom proof_of_sort_array_safety_wit_5 : sort_array_safety_wit_5.
Axiom proof_of_sort_array_safety_wit_6 : sort_array_safety_wit_6.
Axiom proof_of_sort_array_safety_wit_7 : sort_array_safety_wit_7.
Axiom proof_of_sort_array_safety_wit_8 : sort_array_safety_wit_8.
Axiom proof_of_sort_array_safety_wit_9 : sort_array_safety_wit_9.
Axiom proof_of_sort_array_safety_wit_10 : sort_array_safety_wit_10.
Axiom proof_of_sort_array_safety_wit_11 : sort_array_safety_wit_11.
Axiom proof_of_sort_array_safety_wit_12 : sort_array_safety_wit_12.
Axiom proof_of_sort_array_safety_wit_13 : sort_array_safety_wit_13.
Axiom proof_of_sort_array_safety_wit_14 : sort_array_safety_wit_14.
Axiom proof_of_sort_array_safety_wit_15 : sort_array_safety_wit_15.
Axiom proof_of_sort_array_safety_wit_16 : sort_array_safety_wit_16.
Axiom proof_of_sort_array_safety_wit_17 : sort_array_safety_wit_17.
Axiom proof_of_sort_array_safety_wit_18 : sort_array_safety_wit_18.
Axiom proof_of_sort_array_safety_wit_19 : sort_array_safety_wit_19.
Axiom proof_of_sort_array_safety_wit_20 : sort_array_safety_wit_20.
Axiom proof_of_sort_array_safety_wit_21 : sort_array_safety_wit_21.
Axiom proof_of_sort_array_safety_wit_22 : sort_array_safety_wit_22.
Axiom proof_of_sort_array_safety_wit_23 : sort_array_safety_wit_23.
Axiom proof_of_sort_array_safety_wit_24 : sort_array_safety_wit_24.
Axiom proof_of_sort_array_safety_wit_25 : sort_array_safety_wit_25.
Axiom proof_of_sort_array_safety_wit_26 : sort_array_safety_wit_26.
Axiom proof_of_sort_array_safety_wit_27 : sort_array_safety_wit_27.
Axiom proof_of_sort_array_safety_wit_28 : sort_array_safety_wit_28.
Axiom proof_of_sort_array_safety_wit_29 : sort_array_safety_wit_29.
Axiom proof_of_sort_array_safety_wit_30 : sort_array_safety_wit_30.
Axiom proof_of_sort_array_safety_wit_31 : sort_array_safety_wit_31.
Axiom proof_of_sort_array_safety_wit_32 : sort_array_safety_wit_32.
Axiom proof_of_sort_array_safety_wit_33 : sort_array_safety_wit_33.
Axiom proof_of_sort_array_safety_wit_34 : sort_array_safety_wit_34.
Axiom proof_of_sort_array_safety_wit_35 : sort_array_safety_wit_35.
Axiom proof_of_sort_array_safety_wit_36 : sort_array_safety_wit_36.
Axiom proof_of_sort_array_safety_wit_37 : sort_array_safety_wit_37.
Axiom proof_of_sort_array_safety_wit_38 : sort_array_safety_wit_38.
Axiom proof_of_sort_array_safety_wit_39 : sort_array_safety_wit_39.
Axiom proof_of_sort_array_safety_wit_40 : sort_array_safety_wit_40.
Axiom proof_of_sort_array_safety_wit_41 : sort_array_safety_wit_41.
Axiom proof_of_sort_array_safety_wit_42 : sort_array_safety_wit_42.
Axiom proof_of_sort_array_safety_wit_43 : sort_array_safety_wit_43.
Axiom proof_of_sort_array_safety_wit_44 : sort_array_safety_wit_44.
Axiom proof_of_sort_array_safety_wit_45 : sort_array_safety_wit_45.
Axiom proof_of_sort_array_safety_wit_46 : sort_array_safety_wit_46.
Axiom proof_of_sort_array_safety_wit_47 : sort_array_safety_wit_47.
Axiom proof_of_sort_array_safety_wit_48 : sort_array_safety_wit_48.
Axiom proof_of_sort_array_entail_wit_1 : sort_array_entail_wit_1.
Axiom proof_of_sort_array_entail_wit_2 : sort_array_entail_wit_2.
Axiom proof_of_sort_array_entail_wit_3 : sort_array_entail_wit_3.
Axiom proof_of_sort_array_entail_wit_4 : sort_array_entail_wit_4.
Axiom proof_of_sort_array_entail_wit_5 : sort_array_entail_wit_5.
Axiom proof_of_sort_array_entail_wit_6 : sort_array_entail_wit_6.
Axiom proof_of_sort_array_entail_wit_7 : sort_array_entail_wit_7.
Axiom proof_of_sort_array_entail_wit_8 : sort_array_entail_wit_8.
Axiom proof_of_sort_array_entail_wit_9 : sort_array_entail_wit_9.
Axiom proof_of_sort_array_entail_wit_10 : sort_array_entail_wit_10.
Axiom proof_of_sort_array_entail_wit_11 : sort_array_entail_wit_11.
Axiom proof_of_sort_array_entail_wit_12 : sort_array_entail_wit_12.
Axiom proof_of_sort_array_entail_wit_13 : sort_array_entail_wit_13.
Axiom proof_of_sort_array_entail_wit_14 : sort_array_entail_wit_14.
Axiom proof_of_sort_array_entail_wit_15_1 : sort_array_entail_wit_15_1.
Axiom proof_of_sort_array_entail_wit_15_2 : sort_array_entail_wit_15_2.
Axiom proof_of_sort_array_entail_wit_15_3 : sort_array_entail_wit_15_3.
Axiom proof_of_sort_array_entail_wit_15_4 : sort_array_entail_wit_15_4.
Axiom proof_of_sort_array_entail_wit_16 : sort_array_entail_wit_16.
Axiom proof_of_sort_array_entail_wit_17 : sort_array_entail_wit_17.
Axiom proof_of_sort_array_return_wit_1 : sort_array_return_wit_1.
Axiom proof_of_sort_array_partial_solve_wit_1 : sort_array_partial_solve_wit_1.
Axiom proof_of_sort_array_partial_solve_wit_2_pure : sort_array_partial_solve_wit_2_pure.
Axiom proof_of_sort_array_partial_solve_wit_2 : sort_array_partial_solve_wit_2.
Axiom proof_of_sort_array_partial_solve_wit_3 : sort_array_partial_solve_wit_3.
Axiom proof_of_sort_array_partial_solve_wit_4 : sort_array_partial_solve_wit_4.
Axiom proof_of_sort_array_partial_solve_wit_5_pure : sort_array_partial_solve_wit_5_pure.
Axiom proof_of_sort_array_partial_solve_wit_5 : sort_array_partial_solve_wit_5.
Axiom proof_of_sort_array_partial_solve_wit_6 : sort_array_partial_solve_wit_6.
Axiom proof_of_sort_array_partial_solve_wit_7_pure : sort_array_partial_solve_wit_7_pure.
Axiom proof_of_sort_array_partial_solve_wit_7 : sort_array_partial_solve_wit_7.
Axiom proof_of_sort_array_partial_solve_wit_8 : sort_array_partial_solve_wit_8.
Axiom proof_of_sort_array_partial_solve_wit_9 : sort_array_partial_solve_wit_9.
Axiom proof_of_sort_array_partial_solve_wit_10 : sort_array_partial_solve_wit_10.
Axiom proof_of_sort_array_partial_solve_wit_11 : sort_array_partial_solve_wit_11.
Axiom proof_of_sort_array_partial_solve_wit_12 : sort_array_partial_solve_wit_12.
Axiom proof_of_sort_array_partial_solve_wit_13 : sort_array_partial_solve_wit_13.
Axiom proof_of_sort_array_partial_solve_wit_14 : sort_array_partial_solve_wit_14.
Axiom proof_of_sort_array_partial_solve_wit_15 : sort_array_partial_solve_wit_15.
Axiom proof_of_sort_array_partial_solve_wit_16 : sort_array_partial_solve_wit_16.
Axiom proof_of_sort_array_partial_solve_wit_17 : sort_array_partial_solve_wit_17.
Axiom proof_of_sort_array_partial_solve_wit_18 : sort_array_partial_solve_wit_18.
Axiom proof_of_sort_array_partial_solve_wit_19 : sort_array_partial_solve_wit_19.
Axiom proof_of_sort_array_partial_solve_wit_20 : sort_array_partial_solve_wit_20.
Axiom proof_of_sort_array_partial_solve_wit_21 : sort_array_partial_solve_wit_21.
Axiom proof_of_sort_array_partial_solve_wit_22 : sort_array_partial_solve_wit_22.
Axiom proof_of_sort_array_partial_solve_wit_23 : sort_array_partial_solve_wit_23.
Axiom proof_of_sort_array_partial_solve_wit_24 : sort_array_partial_solve_wit_24.
Axiom proof_of_sort_array_partial_solve_wit_25 : sort_array_partial_solve_wit_25.
Axiom proof_of_sort_array_partial_solve_wit_26 : sort_array_partial_solve_wit_26.
Axiom proof_of_sort_array_partial_solve_wit_27 : sort_array_partial_solve_wit_27.
Axiom proof_of_sort_array_partial_solve_wit_28 : sort_array_partial_solve_wit_28.
Axiom proof_of_sort_array_partial_solve_wit_29 : sort_array_partial_solve_wit_29.
Axiom proof_of_sort_array_partial_solve_wit_30 : sort_array_partial_solve_wit_30.
Axiom proof_of_sort_array_partial_solve_wit_31_pure : sort_array_partial_solve_wit_31_pure.
Axiom proof_of_sort_array_partial_solve_wit_31 : sort_array_partial_solve_wit_31.

End VC_Correct.
