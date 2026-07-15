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
Require Import coins_104.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function unique_digits -----*)

Definition unique_digits_safety_wit_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_size_pre)) (PreH3 : (x_size_pre < INT_MAX)) (PreH4 : (x_size_pre = (Zlength (input_l)))) (PreH5 : (problem_104_pre_z input_l )) (PreH6 : (unique_digits_safe_104 input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 x_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 x_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_4 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i < x_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= x_size_pre)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_l)))) (PreH14 : (unique_digits_prefix_104 input_l i output_l )) ,
  ((( &( "u" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition unique_digits_safety_wit_5 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i < x_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= x_size_pre)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_l)))) (PreH14 : (unique_digits_prefix_104 input_l i output_l )) ,
  ((( &( "u" ) )) # Int  |-> 1)
  **  ((( &( "num" ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_6 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input_l 0) = 0)) (PreH2 : (i < x_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= x_size_pre)) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_l)))) (PreH15 : (unique_digits_prefix_104 input_l i output_l )) ,
  ((( &( "u" ) )) # Int  |-> 1)
  **  ((( &( "num" ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_7 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_8 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_9 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u = 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 1)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_10 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u <> 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 0)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_11 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u <> 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 1)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ ((num <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition unique_digits_safety_wit_12 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u <> 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 1)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition unique_digits_safety_wit_13 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u <> 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 1)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_14 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((num % ( 2 ) ) = 0)) (PreH2 : (u <> 0)) (PreH3 : (num > 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= x_size_pre)) (PreH7 : (x_size_pre < INT_MAX)) (PreH8 : (x_size_pre = (Zlength (input_l)))) (PreH9 : (problem_104_pre_z input_l )) (PreH10 : (unique_digits_safe_104 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < x_size_pre)) (PreH13 : (current = (Znth (i) (input_l) (0)))) (PreH14 : (0 < current)) (PreH15 : (current < INT_MAX)) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= i)) (PreH18 : (output_size = (Zlength (output_l)))) (PreH19 : (unique_digits_prefix_104 input_l i output_l )) (PreH20 : (0 <= num)) (PreH21 : (num <= current)) (PreH22 : (u = 1)) (PreH23 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unique_digits_safety_wit_15 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((num % ( 2 ) ) = 0)) (PreH2 : (u <> 0)) (PreH3 : (num > 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= x_size_pre)) (PreH7 : (x_size_pre < INT_MAX)) (PreH8 : (x_size_pre = (Zlength (input_l)))) (PreH9 : (problem_104_pre_z input_l )) (PreH10 : (unique_digits_safe_104 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < x_size_pre)) (PreH13 : (current = (Znth (i) (input_l) (0)))) (PreH14 : (0 < current)) (PreH15 : (current < INT_MAX)) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= i)) (PreH18 : (output_size = (Zlength (output_l)))) (PreH19 : (unique_digits_prefix_104 input_l i output_l )) (PreH20 : (0 <= num)) (PreH21 : (num <= current)) (PreH22 : (u = 1)) (PreH23 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ ((num <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition unique_digits_safety_wit_16 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((num % ( 2 ) ) = 0)) (PreH2 : (u <> 0)) (PreH3 : (num > 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= x_size_pre)) (PreH7 : (x_size_pre < INT_MAX)) (PreH8 : (x_size_pre = (Zlength (input_l)))) (PreH9 : (problem_104_pre_z input_l )) (PreH10 : (unique_digits_safe_104 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < x_size_pre)) (PreH13 : (current = (Znth (i) (input_l) (0)))) (PreH14 : (0 < current)) (PreH15 : (current < INT_MAX)) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= i)) (PreH18 : (output_size = (Zlength (output_l)))) (PreH19 : (unique_digits_prefix_104 input_l i output_l )) (PreH20 : (0 <= num)) (PreH21 : (num <= current)) (PreH22 : (u = 1)) (PreH23 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition unique_digits_safety_wit_17 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((num % ( 2 ) ) <> 0)) (PreH2 : (u <> 0)) (PreH3 : (num > 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= x_size_pre)) (PreH7 : (x_size_pre < INT_MAX)) (PreH8 : (x_size_pre = (Zlength (input_l)))) (PreH9 : (problem_104_pre_z input_l )) (PreH10 : (unique_digits_safe_104 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < x_size_pre)) (PreH13 : (current = (Znth (i) (input_l) (0)))) (PreH14 : (0 < current)) (PreH15 : (current < INT_MAX)) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= i)) (PreH18 : (output_size = (Zlength (output_l)))) (PreH19 : (unique_digits_prefix_104 input_l i output_l )) (PreH20 : (0 <= num)) (PreH21 : (num <= current)) (PreH22 : (u = 1)) (PreH23 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ ((num <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition unique_digits_safety_wit_18 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((num % ( 2 ) ) <> 0)) (PreH2 : (u <> 0)) (PreH3 : (num > 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= x_size_pre)) (PreH7 : (x_size_pre < INT_MAX)) (PreH8 : (x_size_pre = (Zlength (input_l)))) (PreH9 : (problem_104_pre_z input_l )) (PreH10 : (unique_digits_safe_104 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < x_size_pre)) (PreH13 : (current = (Znth (i) (input_l) (0)))) (PreH14 : (0 < current)) (PreH15 : (current < INT_MAX)) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= i)) (PreH18 : (output_size = (Zlength (output_l)))) (PreH19 : (unique_digits_prefix_104 input_l i output_l )) (PreH20 : (0 <= num)) (PreH21 : (num <= current)) (PreH22 : (u = 1)) (PreH23 : (odd_digit_scan_state_104 current num u )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition unique_digits_safety_wit_19 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u = 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_20 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u = 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_21 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u = 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_22 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_23 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_24 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ False ”
.

Definition unique_digits_safety_wit_25 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l) ((cons (current) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition unique_digits_safety_wit_26 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l) ((cons (current) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition unique_digits_safety_wit_27 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l) ((cons (current) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition unique_digits_safety_wit_28 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u = 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition unique_digits_safety_wit_29 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= x_size_pre)) (PreH10 : (output_size = (Zlength (output_l)))) (PreH11 : (unique_digits_prefix_104 input_l x_size_pre output_l )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> x_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition unique_digits_entail_wit_1 := 
(
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) ,
  (IntArray.undef_full retval_2 x_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  EX (output_l: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l 0 output_l ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 x_size_pre )
) \/
(
forall (x_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l 0 (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  emp
).

Definition unique_digits_entail_wit_1_split_goal_1 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l 0 (@nil Z) ) ”
.

Definition unique_digits_entail_wit_1_split_goal_2 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition unique_digits_entail_wit_2_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input_l 0) = 0)) (PreH2 : (i < x_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= x_size_pre)) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_l_2)))) (PreH15 : (unique_digits_prefix_104 input_l i output_l_2 )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= (Znth i input_l 0)) ” 
  &&  “ (0 = 1) ” 
  &&  “ (odd_digit_scan_state_104 (Znth i input_l 0) (Znth i input_l 0) 0 ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= (Znth i input_l 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (odd_digit_scan_state_104 (Znth i input_l 0) (Znth i input_l 0) 0 ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_2_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input_l 0) <> 0)) (PreH2 : (i < x_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= x_size_pre)) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_l_2)))) (PreH15 : (unique_digits_prefix_104 input_l i output_l_2 )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= (Znth i input_l 0)) ” 
  &&  “ (1 = 1) ” 
  &&  “ (odd_digit_scan_state_104 (Znth i input_l 0) (Znth i input_l 0) 1 ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= (Znth i input_l 0)) ” 
  &&  “ (1 = 0) ” 
  &&  “ (odd_digit_scan_state_104 (Znth i input_l 0) (Znth i input_l 0) 1 ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_3_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (num <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < x_size_pre)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (0 < current)) (PreH13 : (current < INT_MAX)) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= i)) (PreH16 : (output_size = (Zlength (output_l)))) (PreH17 : (unique_digits_prefix_104 input_l i output_l )) (PreH18 : (0 <= num)) (PreH19 : (num <= current)) (PreH20 : (u = 0)) (PreH21 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (“ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l_2: (@list Z)) ,
  “ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l_2))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l_2 ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (“ (u = 0) ” 
  &&  “ (num > 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_3_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (num <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < x_size_pre)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (0 < current)) (PreH13 : (current < INT_MAX)) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= i)) (PreH16 : (output_size = (Zlength (output_l_2)))) (PreH17 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH18 : (0 <= num)) (PreH19 : (num <= current)) (PreH20 : (u = 1)) (PreH21 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (“ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l_2))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l_2 ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (u = 0) ” 
  &&  “ (num > 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_3_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u = 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l_2)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 1)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (“ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l_2))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l_2 ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (u = 0) ” 
  &&  “ (num > 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_3_4 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u = 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 0)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (“ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l_2: (@list Z)) ,
  “ (num <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l_2))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l_2 ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (“ (u = 0) ” 
  &&  “ (num > 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_4_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u <> 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 1)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (u <> 0) ” 
  &&  “ (num > 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_4_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u <> 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l_2)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 0)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  EX (output_l: (@list Z)) ,
  “ (u <> 0) ” 
  &&  “ (num > 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (odd_digit_scan_state_104 current num u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_5_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((num % ( 2 ) ) = 0)) (PreH2 : (u <> 0)) (PreH3 : (num > 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= x_size_pre)) (PreH7 : (x_size_pre < INT_MAX)) (PreH8 : (x_size_pre = (Zlength (input_l)))) (PreH9 : (problem_104_pre_z input_l )) (PreH10 : (unique_digits_safe_104 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < x_size_pre)) (PreH13 : (current = (Znth (i) (input_l) (0)))) (PreH14 : (0 < current)) (PreH15 : (current < INT_MAX)) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= i)) (PreH18 : (output_size = (Zlength (output_l_2)))) (PreH19 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH20 : (0 <= num)) (PreH21 : (num <= current)) (PreH22 : (u = 1)) (PreH23 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (num ÷ 10 )) ” 
  &&  “ ((num ÷ 10 ) <= current) ” 
  &&  “ (0 = 1) ” 
  &&  “ (odd_digit_scan_state_104 current (num ÷ 10 ) 0 ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (num ÷ 10 )) ” 
  &&  “ ((num ÷ 10 ) <= current) ” 
  &&  “ (0 = 0) ” 
  &&  “ (odd_digit_scan_state_104 current (num ÷ 10 ) 0 ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_5_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((num % ( 2 ) ) <> 0)) (PreH2 : (u <> 0)) (PreH3 : (num > 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= x_size_pre)) (PreH7 : (x_size_pre < INT_MAX)) (PreH8 : (x_size_pre = (Zlength (input_l)))) (PreH9 : (problem_104_pre_z input_l )) (PreH10 : (unique_digits_safe_104 input_l )) (PreH11 : (0 <= i)) (PreH12 : (i < x_size_pre)) (PreH13 : (current = (Znth (i) (input_l) (0)))) (PreH14 : (0 < current)) (PreH15 : (current < INT_MAX)) (PreH16 : (0 <= output_size)) (PreH17 : (output_size <= i)) (PreH18 : (output_size = (Zlength (output_l_2)))) (PreH19 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH20 : (0 <= num)) (PreH21 : (num <= current)) (PreH22 : (u = 1)) (PreH23 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (num ÷ 10 )) ” 
  &&  “ ((num ÷ 10 ) <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (odd_digit_scan_state_104 current (num ÷ 10 ) u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= (num ÷ 10 )) ” 
  &&  “ ((num ÷ 10 ) <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (odd_digit_scan_state_104 current (num ÷ 10 ) u ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_6_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (u = 0)) (PreH2 : (num > 0)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : (x_size_pre = (Zlength (input_l)))) (PreH8 : (problem_104_pre_z input_l )) (PreH9 : (unique_digits_safe_104 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i < x_size_pre)) (PreH12 : (current = (Znth (i) (input_l) (0)))) (PreH13 : (0 < current)) (PreH14 : (current < INT_MAX)) (PreH15 : (0 <= output_size)) (PreH16 : (output_size <= i)) (PreH17 : (output_size = (Zlength (output_l_2)))) (PreH18 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH19 : (0 <= num)) (PreH20 : (num <= current)) (PreH21 : (u = 0)) (PreH22 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_6_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (num <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < x_size_pre)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (0 < current)) (PreH13 : (current < INT_MAX)) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= i)) (PreH16 : (output_size = (Zlength (output_l_2)))) (PreH17 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH18 : (0 <= num)) (PreH19 : (num <= current)) (PreH20 : (u = 1)) (PreH21 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_6_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (u: Z) (num: Z) (output_l_2: (@list Z)) (output_size: Z) (current: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (num <= 0)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i < x_size_pre)) (PreH11 : (current = (Znth (i) (input_l) (0)))) (PreH12 : (0 < current)) (PreH13 : (current < INT_MAX)) (PreH14 : (0 <= output_size)) (PreH15 : (output_size <= i)) (PreH16 : (output_size = (Zlength (output_l_2)))) (PreH17 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH18 : (0 <= num)) (PreH19 : (num <= current)) (PreH20 : (u = 0)) (PreH21 : (odd_digit_scan_state_104 current num u )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre ))
.

Definition unique_digits_entail_wit_7_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u = 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ” 
  &&  “ (u = 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_7_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u = 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ” 
  &&  “ (u = 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_7_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u = 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ” 
  &&  “ (u = 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_7_4 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u = 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (has_even_digit_z_104 current ) ” 
  &&  “ (u = 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_8_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ” 
  &&  “ (u <> 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_8_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ” 
  &&  “ (u <> 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_8_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ” 
  &&  “ (u <> 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_8_4 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ” 
  &&  “ (u <> 0) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_9_1 := 
(
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l_2)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l_2) ((cons (current) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= x_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l (i + 1 ) output_l ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
) \/
(
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l_2)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l (i + 1 ) (app (output_l_2) ((cons (current) ((@nil Z))))) ) ” 
  &&  “ ((output_size + 1 ) = (Zlength ((app (output_l_2) ((cons (current) ((@nil Z)))))))) ”
  &&  emp
).

Definition unique_digits_entail_wit_9_1_split_goal_1 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l_2)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l (i + 1 ) (app (output_l_2) ((cons (current) ((@nil Z))))) ) ”
.

Definition unique_digits_entail_wit_9_1_split_goal_2 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l_2)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  TT && emp 
|--
  “ ((output_size + 1 ) = (Zlength ((app (output_l_2) ((cons (current) ((@nil Z)))))))) ”
.

Definition unique_digits_entail_wit_9_2 := 
(
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l_2)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u = 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= x_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l (i + 1 ) output_l ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
) \/
(
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l_2)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u = 0)) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l (i + 1 ) output_l_2 ) ”
  &&  emp
).

Definition unique_digits_entail_wit_9_2_split_goal_1 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l_2)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l_2 )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 0)) (PreH20 : (u = 0)) (PreH21 : (has_even_digit_z_104 current )) (PreH22 : (u = 0)) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l (i + 1 ) output_l_2 ) ”
.

Definition unique_digits_entail_wit_10 := 
(
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i >= x_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= x_size_pre)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_l_2)))) (PreH14 : (unique_digits_prefix_104 input_l i output_l_2 )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= x_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l x_size_pre output_l ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> x_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
) \/
(
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i >= x_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= x_size_pre)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_l_2)))) (PreH14 : (unique_digits_prefix_104 input_l i output_l_2 )) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l x_size_pre output_l_2 ) ”
  &&  emp
).

Definition unique_digits_entail_wit_10_split_goal_1 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i >= x_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= x_size_pre)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_l_2)))) (PreH14 : (unique_digits_prefix_104 input_l i output_l_2 )) ,
  TT && emp 
|--
  “ (unique_digits_prefix_104 input_l x_size_pre output_l_2 ) ”
.

Definition unique_digits_entail_wit_11 := 
(
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (output_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (output_size = (Zlength (sorted_l_2)))) (PreH2 : (x_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= x_size_pre)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (output_size) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation output_l_2 sorted_l_2 )) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= x_size_pre)) (PreH13 : (x_size_pre < INT_MAX)) (PreH14 : (x_size_pre = (Zlength (input_l)))) (PreH15 : (problem_104_pre_z input_l )) (PreH16 : (unique_digits_safe_104 input_l )) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= x_size_pre)) (PreH19 : (output_size = (Zlength (output_l_2)))) (PreH20 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) ,
  (IntArray.full data x_size_pre sorted_full_l )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (data_l: (@list Z))  (sorted_l: (@list Z))  (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= x_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_size = (Zlength (sorted_l))) ” 
  &&  “ (x_size_pre = (Zlength (data_l))) ” 
  &&  “ ((sublist (0) (output_size) (data_l)) = sorted_l) ” 
  &&  “ (unique_digits_prefix_104 input_l x_size_pre output_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation output_l sorted_l ) ” 
  &&  “ (problem_104_spec_z input_l sorted_l ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full data x_size_pre data_l )
) \/
(
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (output_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (output_size = (Zlength (sorted_l_2)))) (PreH2 : (x_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= x_size_pre)) (PreH5 : (0 <= x_size_pre)) (PreH6 : (x_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (output_size) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation output_l_2 sorted_l_2 )) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= x_size_pre)) (PreH13 : (x_size_pre < INT_MAX)) (PreH14 : (x_size_pre = (Zlength (input_l)))) (PreH15 : (problem_104_pre_z input_l )) (PreH16 : (unique_digits_safe_104 input_l )) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= x_size_pre)) (PreH19 : (output_size = (Zlength (output_l_2)))) (PreH20 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) ,
  TT && emp 
|--
  EX (output_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= x_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_size = (Zlength ((sublist (0) (output_size) (sorted_full_l))))) ” 
  &&  “ (x_size_pre = (Zlength (sorted_full_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l x_size_pre output_l ) ” 
  &&  “ (sorted_int_list_by 1 (sublist (0) (output_size) (sorted_full_l)) ) ” 
  &&  “ (Permutation output_l (sublist (0) (output_size) (sorted_full_l)) ) ” 
  &&  “ (problem_104_spec_z input_l (sublist (0) (output_size) (sorted_full_l)) ) ”
  &&  emp
).

Definition unique_digits_return_wit_1 := 
(
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.full data_2 x_size_pre data_l_2 )
|--
  EX (data_l: (@list Z))  (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= x_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (x_size_pre = (Zlength (data_l))) ” 
  &&  “ ((sublist (0) (output_size) (data_l)) = output_l) ” 
  &&  “ (problem_104_spec_z input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data x_size_pre data_l )
  **  (IntArray.full x_pre x_size_pre input_l )
) \/
(
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ (problem_104_spec_z input_l (sublist (0) ((Zlength (output_l))) (data_l_2)) ) ” 
  &&  “ ((sublist (0) ((Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) (data_l_2)) = (sublist (0) ((Zlength (output_l))) (data_l_2))) ” 
  &&  “ ((Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2)))) <= x_size_pre) ” 
  &&  “ (0 <= (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ” 
  &&  “ (output_size_2 = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ” 
  &&  “ (output_size_2 = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ” 
  &&  “ (output_size_2 = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ”
  &&  emp
).

Definition unique_digits_return_wit_1_split_goal_1 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ (problem_104_spec_z input_l (sublist (0) ((Zlength (output_l))) (data_l_2)) ) ”
.

Definition unique_digits_return_wit_1_split_goal_2 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ ((sublist (0) ((Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) (data_l_2)) = (sublist (0) ((Zlength (output_l))) (data_l_2))) ”
.

Definition unique_digits_return_wit_1_split_goal_3 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ ((Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2)))) <= x_size_pre) ”
.

Definition unique_digits_return_wit_1_split_goal_4 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ (0 <= (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ”
.

Definition unique_digits_return_wit_1_split_goal_5 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ (output_size_2 = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ”
.

Definition unique_digits_return_wit_1_split_goal_6 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ (output_size_2 = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ”
.

Definition unique_digits_return_wit_1_split_goal_7 := 
forall (x_size_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= x_size_pre)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_size_2 = (Zlength (sorted_l)))) (PreH12 : (x_size_pre = (Zlength (data_l_2)))) (PreH13 : ((sublist (0) (output_size_2) (data_l_2)) = sorted_l)) (PreH14 : (unique_digits_prefix_104 input_l x_size_pre output_l_2 )) (PreH15 : (sorted_int_list_by 1 sorted_l )) (PreH16 : (Permutation output_l_2 sorted_l )) (PreH17 : (problem_104_spec_z input_l sorted_l )) ,
  TT && emp 
|--
  “ (output_size_2 = (Zlength ((sublist (0) ((Zlength (output_l))) (data_l_2))))) ”
.

Definition unique_digits_partial_solve_wit_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= x_size_pre)) (PreH2 : (x_size_pre < INT_MAX)) (PreH3 : (x_size_pre = (Zlength (input_l)))) (PreH4 : (problem_104_pre_z input_l )) (PreH5 : (unique_digits_safe_104 input_l )) ,
  (IntArray.full x_pre x_size_pre input_l )
|--
  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ”
  &&  (IntArray.full x_pre x_size_pre input_l )
.

Definition unique_digits_partial_solve_wit_2_pure := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_size_pre)) (PreH3 : (x_size_pre < INT_MAX)) (PreH4 : (x_size_pre = (Zlength (input_l)))) (PreH5 : (problem_104_pre_z input_l )) (PreH6 : (unique_digits_safe_104 input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  “ (x_size_pre >= 0) ” 
  &&  “ (x_size_pre < INT_MAX) ”
.

Definition unique_digits_partial_solve_wit_2_aux := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_size_pre)) (PreH3 : (x_size_pre < INT_MAX)) (PreH4 : (x_size_pre = (Zlength (input_l)))) (PreH5 : (problem_104_pre_z input_l )) (PreH6 : (unique_digits_safe_104 input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  “ (x_size_pre >= 0) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
.

Definition unique_digits_partial_solve_wit_2 := unique_digits_partial_solve_wit_2_pure -> unique_digits_partial_solve_wit_2_aux.

Definition unique_digits_partial_solve_wit_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i < x_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (0 <= x_size_pre)) (PreH5 : (x_size_pre < INT_MAX)) (PreH6 : (x_size_pre = (Zlength (input_l)))) (PreH7 : (problem_104_pre_z input_l )) (PreH8 : (unique_digits_safe_104 input_l )) (PreH9 : (0 <= i)) (PreH10 : (i <= x_size_pre)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_l)))) (PreH14 : (unique_digits_prefix_104 input_l i output_l )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (i < x_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= x_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ”
  &&  (((x_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i x_pre i 0 x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_partial_solve_wit_4 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (current: Z) (output_size: Z) (num: Z) (u: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < x_size_pre)) (PreH10 : (current = (Znth (i) (input_l) (0)))) (PreH11 : (0 < current)) (PreH12 : (current < INT_MAX)) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_l)))) (PreH16 : (unique_digits_prefix_104 input_l i output_l )) (PreH17 : (0 <= num)) (PreH18 : (num <= current)) (PreH19 : (u = 1)) (PreH20 : (u <> 0)) (PreH21 : (only_odd_digits_z_104 current )) (PreH22 : (u <> 0)) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < x_size_pre) ” 
  &&  “ (current = (Znth (i) (input_l) (0))) ” 
  &&  “ (0 < current) ” 
  &&  “ (current < INT_MAX) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l i output_l ) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= current) ” 
  &&  “ (u = 1) ” 
  &&  “ (u <> 0) ” 
  &&  “ (only_odd_digits_z_104 current ) ” 
  &&  “ (u <> 0) ”
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition unique_digits_partial_solve_wit_5_pure := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= x_size_pre)) (PreH10 : (output_size = (Zlength (output_l)))) (PreH11 : (unique_digits_prefix_104 input_l x_size_pre output_l )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> x_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (data <> 0) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= x_size_pre) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ”
.

Definition unique_digits_partial_solve_wit_5_aux := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (0 <= x_size_pre)) (PreH4 : (x_size_pre < INT_MAX)) (PreH5 : (x_size_pre = (Zlength (input_l)))) (PreH6 : (problem_104_pre_z input_l )) (PreH7 : (unique_digits_safe_104 input_l )) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= x_size_pre)) (PreH10 : (output_size = (Zlength (output_l)))) (PreH11 : (unique_digits_prefix_104 input_l x_size_pre output_l )) ,
  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  “ (data <> 0) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= x_size_pre) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= x_size_pre) ” 
  &&  “ (x_size_pre < INT_MAX) ” 
  &&  “ (x_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_104_pre_z input_l ) ” 
  &&  “ (unique_digits_safe_104 input_l ) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= x_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (unique_digits_prefix_104 input_l x_size_pre output_l ) ”
  &&  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition unique_digits_partial_solve_wit_5 := unique_digits_partial_solve_wit_5_pure -> unique_digits_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_unique_digits_safety_wit_1 : unique_digits_safety_wit_1.
Axiom proof_of_unique_digits_safety_wit_2 : unique_digits_safety_wit_2.
Axiom proof_of_unique_digits_safety_wit_3 : unique_digits_safety_wit_3.
Axiom proof_of_unique_digits_safety_wit_4 : unique_digits_safety_wit_4.
Axiom proof_of_unique_digits_safety_wit_5 : unique_digits_safety_wit_5.
Axiom proof_of_unique_digits_safety_wit_6 : unique_digits_safety_wit_6.
Axiom proof_of_unique_digits_safety_wit_7 : unique_digits_safety_wit_7.
Axiom proof_of_unique_digits_safety_wit_8 : unique_digits_safety_wit_8.
Axiom proof_of_unique_digits_safety_wit_9 : unique_digits_safety_wit_9.
Axiom proof_of_unique_digits_safety_wit_10 : unique_digits_safety_wit_10.
Axiom proof_of_unique_digits_safety_wit_11 : unique_digits_safety_wit_11.
Axiom proof_of_unique_digits_safety_wit_12 : unique_digits_safety_wit_12.
Axiom proof_of_unique_digits_safety_wit_13 : unique_digits_safety_wit_13.
Axiom proof_of_unique_digits_safety_wit_14 : unique_digits_safety_wit_14.
Axiom proof_of_unique_digits_safety_wit_15 : unique_digits_safety_wit_15.
Axiom proof_of_unique_digits_safety_wit_16 : unique_digits_safety_wit_16.
Axiom proof_of_unique_digits_safety_wit_17 : unique_digits_safety_wit_17.
Axiom proof_of_unique_digits_safety_wit_18 : unique_digits_safety_wit_18.
Axiom proof_of_unique_digits_safety_wit_19 : unique_digits_safety_wit_19.
Axiom proof_of_unique_digits_safety_wit_20 : unique_digits_safety_wit_20.
Axiom proof_of_unique_digits_safety_wit_21 : unique_digits_safety_wit_21.
Axiom proof_of_unique_digits_safety_wit_22 : unique_digits_safety_wit_22.
Axiom proof_of_unique_digits_safety_wit_23 : unique_digits_safety_wit_23.
Axiom proof_of_unique_digits_safety_wit_24 : unique_digits_safety_wit_24.
Axiom proof_of_unique_digits_safety_wit_25 : unique_digits_safety_wit_25.
Axiom proof_of_unique_digits_safety_wit_26 : unique_digits_safety_wit_26.
Axiom proof_of_unique_digits_safety_wit_27 : unique_digits_safety_wit_27.
Axiom proof_of_unique_digits_safety_wit_28 : unique_digits_safety_wit_28.
Axiom proof_of_unique_digits_safety_wit_29 : unique_digits_safety_wit_29.
Axiom proof_of_unique_digits_entail_wit_1 : unique_digits_entail_wit_1.
Axiom proof_of_unique_digits_entail_wit_2_1 : unique_digits_entail_wit_2_1.
Axiom proof_of_unique_digits_entail_wit_2_2 : unique_digits_entail_wit_2_2.
Axiom proof_of_unique_digits_entail_wit_3_1 : unique_digits_entail_wit_3_1.
Axiom proof_of_unique_digits_entail_wit_3_2 : unique_digits_entail_wit_3_2.
Axiom proof_of_unique_digits_entail_wit_3_3 : unique_digits_entail_wit_3_3.
Axiom proof_of_unique_digits_entail_wit_3_4 : unique_digits_entail_wit_3_4.
Axiom proof_of_unique_digits_entail_wit_4_1 : unique_digits_entail_wit_4_1.
Axiom proof_of_unique_digits_entail_wit_4_2 : unique_digits_entail_wit_4_2.
Axiom proof_of_unique_digits_entail_wit_5_1 : unique_digits_entail_wit_5_1.
Axiom proof_of_unique_digits_entail_wit_5_2 : unique_digits_entail_wit_5_2.
Axiom proof_of_unique_digits_entail_wit_6_1 : unique_digits_entail_wit_6_1.
Axiom proof_of_unique_digits_entail_wit_6_2 : unique_digits_entail_wit_6_2.
Axiom proof_of_unique_digits_entail_wit_6_3 : unique_digits_entail_wit_6_3.
Axiom proof_of_unique_digits_entail_wit_7_1 : unique_digits_entail_wit_7_1.
Axiom proof_of_unique_digits_entail_wit_7_2 : unique_digits_entail_wit_7_2.
Axiom proof_of_unique_digits_entail_wit_7_3 : unique_digits_entail_wit_7_3.
Axiom proof_of_unique_digits_entail_wit_7_4 : unique_digits_entail_wit_7_4.
Axiom proof_of_unique_digits_entail_wit_8_1 : unique_digits_entail_wit_8_1.
Axiom proof_of_unique_digits_entail_wit_8_2 : unique_digits_entail_wit_8_2.
Axiom proof_of_unique_digits_entail_wit_8_3 : unique_digits_entail_wit_8_3.
Axiom proof_of_unique_digits_entail_wit_8_4 : unique_digits_entail_wit_8_4.
Axiom proof_of_unique_digits_entail_wit_9_1 : unique_digits_entail_wit_9_1.
Axiom proof_of_unique_digits_entail_wit_9_2 : unique_digits_entail_wit_9_2.
Axiom proof_of_unique_digits_entail_wit_10 : unique_digits_entail_wit_10.
Axiom proof_of_unique_digits_entail_wit_11 : unique_digits_entail_wit_11.
Axiom proof_of_unique_digits_return_wit_1 : unique_digits_return_wit_1.
Axiom proof_of_unique_digits_partial_solve_wit_1 : unique_digits_partial_solve_wit_1.
Axiom proof_of_unique_digits_partial_solve_wit_2_pure : unique_digits_partial_solve_wit_2_pure.
Axiom proof_of_unique_digits_partial_solve_wit_2 : unique_digits_partial_solve_wit_2.
Axiom proof_of_unique_digits_partial_solve_wit_3 : unique_digits_partial_solve_wit_3.
Axiom proof_of_unique_digits_partial_solve_wit_4 : unique_digits_partial_solve_wit_4.
Axiom proof_of_unique_digits_partial_solve_wit_5_pure : unique_digits_partial_solve_wit_5_pure.
Axiom proof_of_unique_digits_partial_solve_wit_5 : unique_digits_partial_solve_wit_5.

End VC_Correct.
