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
Require Import coins_70.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function strange_sort_list -----*)

Definition strange_sort_list_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full retval_3 lst_size_pre )
  **  ((( &( "sorted" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strange_sort_list_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.seg sorted 0 (i + 1 ) (app ((sublist (0) (i) (input_l))) ((cons ((Znth i input_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strange_sort_list_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strange_sort_list_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strange_sort_list_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) ,
  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strange_sort_list_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) ,
  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ ((lst_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lst_size_pre - 1 )) ”
.

Definition strange_sort_list_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) ,
  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strange_sort_list_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (k: Z) (right: Z) (left: Z) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) (PreH1 : (left < right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l )) (PreH12 : (Permutation input_l sorted_l )) (PreH13 : (0 <= left)) (PreH14 : (left <= lst_size_pre)) (PreH15 : (right = ((lst_size_pre - 1 ) - left ))) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth left sorted_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition strange_sort_list_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition strange_sort_list_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strange_sort_list_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z)))))) ((cons ((Znth right sorted_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "left" ) )) # Int  |-> (left + 1 ))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition strange_sort_list_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z)))))) ((cons ((Znth right sorted_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "left" ) )) # Int  |-> (left + 1 ))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
|--
  “ ((right - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right - 1 )) ”
.

Definition strange_sort_list_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z)))))) ((cons ((Znth right sorted_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "left" ) )) # Int  |-> (left + 1 ))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strange_sort_list_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (left = right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l )) (PreH12 : (Permutation input_l sorted_l )) (PreH13 : (0 <= left)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (left >= right)) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth left sorted_l 0)) ((@nil Z))))) )
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition strange_sort_list_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full retval_3 lst_size_pre )
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  (IntArray.seg retval_3 0 0 (sublist (0) (0) (input_l)) )
  **  (IntArray.undef_seg retval_3 0 lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full retval_2 lst_size_pre )
|--
  “ ((sublist (0) (0) (input_l)) = (@nil Z)) ”
  &&  (IntArray.undef_full retval_2 lst_size_pre )
).

Definition strange_sort_list_entail_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full retval_2 lst_size_pre )
|--
  “ ((sublist (0) (0) (input_l)) = (@nil Z)) ”
.

Definition strange_sort_list_entail_wit_1_split_goal_spatial := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full retval_2 lst_size_pre )
|--
  (IntArray.undef_full retval_2 lst_size_pre )
.

Definition strange_sort_list_entail_wit_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.seg sorted 0 (i + 1 ) (app ((sublist (0) (i) (input_l))) ((cons ((Znth i input_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 (i + 1 ) (sublist (0) ((i + 1 )) (input_l)) )
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.undef_full data lst_size_pre )
|--
  “ ((app ((sublist (0) (i) (input_l))) ((cons ((Znth i input_l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (input_l))) ”
  &&  (IntArray.undef_full data lst_size_pre )
).

Definition strange_sort_list_entail_wit_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.undef_full data lst_size_pre )
|--
  “ ((app ((sublist (0) (i) (input_l))) ((cons ((Znth i input_l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (input_l))) ”
.

Definition strange_sort_list_entail_wit_2_split_goal_spatial := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.undef_full data lst_size_pre )
|--
  (IntArray.undef_full data lst_size_pre )
.

Definition strange_sort_list_entail_wit_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (sublist (0) (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (sublist (0) (i) (input_l)) )
|--
  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
).

Definition strange_sort_list_entail_wit_3_split_goal_spatial := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (sublist (0) (i) (input_l)) )
|--
  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
.

Definition strange_sort_list_entail_wit_4 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (lst_size_pre = (Zlength (sorted_full_l)))) (PreH3 : ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH4 : (sorted_int_list_by 1 sorted_l_2 )) (PreH5 : (Permutation input_l sorted_l_2 )) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (sorted <> 0)) (PreH9 : (0 <= lst_size_pre)) (PreH10 : (lst_size_pre < INT_MAX)) (PreH11 : (lst_size_pre = (Zlength (input_l)))) (PreH12 : (problem_70_pre_z input_l )) (PreH13 : (strange_output_safe_70 input_l )) ,
  (IntArray.full sorted lst_size_pre sorted_full_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (lst_size_pre = (Zlength (sorted_full_l)))) (PreH3 : ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH4 : (sorted_int_list_by 1 sorted_l_2 )) (PreH5 : (Permutation input_l sorted_l_2 )) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (sorted <> 0)) (PreH9 : (0 <= lst_size_pre)) (PreH10 : (lst_size_pre < INT_MAX)) (PreH11 : (lst_size_pre = (Zlength (input_l)))) (PreH12 : (problem_70_pre_z input_l )) (PreH13 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full data lst_size_pre )
|--
  “ (Permutation input_l sorted_full_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_full_l ) ”
  &&  (IntArray.undef_full data lst_size_pre )
).

Definition strange_sort_list_entail_wit_4_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (lst_size_pre = (Zlength (sorted_full_l)))) (PreH3 : ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH4 : (sorted_int_list_by 1 sorted_l_2 )) (PreH5 : (Permutation input_l sorted_l_2 )) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (sorted <> 0)) (PreH9 : (0 <= lst_size_pre)) (PreH10 : (lst_size_pre < INT_MAX)) (PreH11 : (lst_size_pre = (Zlength (input_l)))) (PreH12 : (problem_70_pre_z input_l )) (PreH13 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full data lst_size_pre )
|--
  “ (Permutation input_l sorted_full_l ) ”
.

Definition strange_sort_list_entail_wit_4_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (lst_size_pre = (Zlength (sorted_full_l)))) (PreH3 : ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH4 : (sorted_int_list_by 1 sorted_l_2 )) (PreH5 : (Permutation input_l sorted_l_2 )) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (sorted <> 0)) (PreH9 : (0 <= lst_size_pre)) (PreH10 : (lst_size_pre < INT_MAX)) (PreH11 : (lst_size_pre = (Zlength (input_l)))) (PreH12 : (problem_70_pre_z input_l )) (PreH13 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full data lst_size_pre )
|--
  “ (sorted_int_list_by 1 sorted_full_l ) ”
.

Definition strange_sort_list_entail_wit_4_split_goal_spatial := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (lst_size_pre = (Zlength (sorted_full_l)))) (PreH3 : ((sublist (0) (lst_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH4 : (sorted_int_list_by 1 sorted_l_2 )) (PreH5 : (Permutation input_l sorted_l_2 )) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (sorted <> 0)) (PreH9 : (0 <= lst_size_pre)) (PreH10 : (lst_size_pre < INT_MAX)) (PreH11 : (lst_size_pre = (Zlength (input_l)))) (PreH12 : (problem_70_pre_z input_l )) (PreH13 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full data lst_size_pre )
|--
  (IntArray.undef_full data lst_size_pre )
.

Definition strange_sort_list_entail_wit_5 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ ((lst_size_pre - 1 ) = ((lst_size_pre - 1 ) - 0 )) ” 
  &&  “ (0 = (2 * 0 )) ” 
  &&  “ (0 = (Zlength ((strange_pairs_prefix_70 (sorted_l) (0))))) ” 
  &&  “ (0 <= lst_size_pre) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 0 (strange_pairs_prefix_70 (sorted_l) (0)) )
  **  (IntArray.undef_seg data 0 lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) ,
  TT && emp 
|--
  “ (0 = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (0))))) ” 
  &&  “ ((strange_pairs_prefix_70 (sorted_l_2) (0)) = (@nil Z)) ”
  &&  emp
).

Definition strange_sort_list_entail_wit_5_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) ,
  TT && emp 
|--
  “ (0 = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (0))))) ”
.

Definition strange_sort_list_entail_wit_5_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) ,
  TT && emp 
|--
  “ ((strange_pairs_prefix_70 (sorted_l_2) (0)) = (@nil Z)) ”
.

Definition strange_sort_list_entail_wit_6 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (k: Z) (right: Z) (left: Z) (sorted_l_2: (@list Z)) (sorted: Z) (data: Z) (out: Z) (PreH1 : (left < right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (left <= lst_size_pre)) (PreH15 : (right = ((lst_size_pre - 1 ) - left ))) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth left sorted_l_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ ((k + 1 ) = ((2 * left ) + 1 )) ” 
  &&  “ ((k + 1 ) <= lst_size_pre) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 (k + 1 ) (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (k: Z) (right: Z) (left: Z) (sorted_l_2: (@list Z)) (sorted: Z) (data: Z) (out: Z) (PreH1 : (left < right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (left <= lst_size_pre)) (PreH15 : (right = ((lst_size_pre - 1 ) - left ))) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  TT && emp 
|--
  “ ((app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth left sorted_l_2 0)) ((@nil Z))))) = (app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth (left) (sorted_l_2) (0))) ((@nil Z)))))) ”
  &&  emp
).

Definition strange_sort_list_entail_wit_6_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (k: Z) (right: Z) (left: Z) (sorted_l_2: (@list Z)) (sorted: Z) (data: Z) (out: Z) (PreH1 : (left < right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (left <= lst_size_pre)) (PreH15 : (right = ((lst_size_pre - 1 ) - left ))) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  TT && emp 
|--
  “ ((app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth left sorted_l_2 0)) ((@nil Z))))) = (app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth (left) (sorted_l_2) (0))) ((@nil Z)))))) ”
.

Definition strange_sort_list_entail_wit_7 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth (left) (sorted_l_2) (0))) ((@nil Z)))))) ((cons ((Znth right sorted_l_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= lst_size_pre) ” 
  &&  “ ((right - 1 ) = ((lst_size_pre - 1 ) - (left + 1 ) )) ” 
  &&  “ ((k + 1 ) = (2 * (left + 1 ) )) ” 
  &&  “ ((k + 1 ) = (Zlength ((strange_pairs_prefix_70 (sorted_l) ((left + 1 )))))) ” 
  &&  “ ((k + 1 ) <= lst_size_pre) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 (k + 1 ) (strange_pairs_prefix_70 (sorted_l) ((left + 1 ))) )
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  TT && emp 
|--
  “ ((k + 1 ) = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) ((left + 1 )))))) ” 
  &&  “ ((app ((app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth (left) (sorted_l_2) (0))) ((@nil Z)))))) ((cons ((Znth right sorted_l_2 0)) ((@nil Z))))) = (strange_pairs_prefix_70 (sorted_l_2) ((left + 1 )))) ”
  &&  emp
).

Definition strange_sort_list_entail_wit_7_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  TT && emp 
|--
  “ ((k + 1 ) = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) ((left + 1 )))))) ”
.

Definition strange_sort_list_entail_wit_7_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  TT && emp 
|--
  “ ((app ((app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth (left) (sorted_l_2) (0))) ((@nil Z)))))) ((cons ((Znth right sorted_l_2 0)) ((@nil Z))))) = (strange_pairs_prefix_70 (sorted_l_2) ((left + 1 )))) ”
.

Definition strange_sort_list_entail_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (k: Z) (right: Z) (left: Z) (sorted_l_2: (@list Z)) (sorted: Z) (data: Z) (out: Z) (PreH1 : (left >= right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (left <= lst_size_pre)) (PreH15 : (right = ((lst_size_pre - 1 ) - left ))) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l_2) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ (left >= right) ” 
  &&  “ (k = (2 * left )) ” 
  &&  “ (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left))))) ” 
  &&  “ (k <= lst_size_pre) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
.

Definition strange_sort_list_entail_wit_9_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (left <> right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (left >= right)) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l_2) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (k = lst_size_pre) ” 
  &&  “ ((strange_output_prefix_70 (sorted_l) (lst_size_pre)) = (strange_output_70 (sorted_l))) ” 
  &&  “ (problem_70_spec_z input_l (strange_output_70 (sorted_l)) ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
  **  (IntArray.full_shape sorted lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (left <> right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (left >= right)) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l_2) (left)) )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (k = lst_size_pre) ” 
  &&  “ ((strange_output_prefix_70 (sorted_l) (lst_size_pre)) = (strange_output_70 (sorted_l))) ” 
  &&  “ (problem_70_spec_z input_l (strange_output_70 (sorted_l)) ) ”
  &&  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
  **  (IntArray.full_shape sorted lst_size_pre )
).

Definition strange_sort_list_entail_wit_9_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (left = right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (left >= right)) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth left sorted_l_2 0)) ((@nil Z))))) )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ ((k + 1 ) = lst_size_pre) ” 
  &&  “ ((strange_output_prefix_70 (sorted_l) (lst_size_pre)) = (strange_output_70 (sorted_l))) ” 
  &&  “ (problem_70_spec_z input_l (strange_output_70 (sorted_l)) ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
  **  (IntArray.full_shape sorted lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (left = right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l_2 )) (PreH12 : (Permutation input_l sorted_l_2 )) (PreH13 : (0 <= left)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (left >= right)) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l_2) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.seg data 0 (k + 1 ) (app ((strange_pairs_prefix_70 (sorted_l_2) (left))) ((cons ((Znth left sorted_l_2 0)) ((@nil Z))))) )
  **  (IntArray.full sorted lst_size_pre sorted_l_2 )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ ((k + 1 ) = lst_size_pre) ” 
  &&  “ ((strange_output_prefix_70 (sorted_l) (lst_size_pre)) = (strange_output_70 (sorted_l))) ” 
  &&  “ (problem_70_spec_z input_l (strange_output_70 (sorted_l)) ) ”
  &&  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
  **  (IntArray.full_shape sorted lst_size_pre )
).

Definition strange_sort_list_entail_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l_2 )) (PreH11 : (Permutation input_l sorted_l_2 )) (PreH12 : (k = lst_size_pre)) (PreH13 : ((strange_output_prefix_70 (sorted_l_2) (lst_size_pre)) = (strange_output_70 (sorted_l_2)))) (PreH14 : (problem_70_spec_z input_l (strange_output_70 (sorted_l_2)) )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l_2)) )
  **  (IntArray.full_shape sorted lst_size_pre )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (problem_70_spec_z input_l (strange_output_70 (sorted_l)) ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
  **  (IntArray.full_shape sorted lst_size_pre )
.

Definition strange_sort_list_entail_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l_2)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (problem_70_spec_z input_l (strange_output_70 (sorted_l_2)) )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l_2)) )
|--
  EX (sorted_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (problem_70_spec_z input_l (strange_output_70 (sorted_l)) ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
.

Definition strange_sort_list_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (lst_size_pre = (Zlength (sorted_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (problem_70_spec_z input_l (strange_output_70 (sorted_l)) )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data_2 lst_size_pre (strange_output_70 (sorted_l)) )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = lst_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (problem_70_spec_z input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full data output_size output_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (lst_size_pre = (Zlength (sorted_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (problem_70_spec_z input_l (strange_output_70 (sorted_l)) )) ,
  TT && emp 
|--
  “ (lst_size_pre = (Zlength ((strange_output_70 (sorted_l))))) ”
  &&  emp
).

Definition strange_sort_list_return_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data_2: Z) (PreH1 : (out <> 0)) (PreH2 : (data_2 <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (lst_size_pre = (Zlength (sorted_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (problem_70_spec_z input_l (strange_output_70 (sorted_l)) )) ,
  TT && emp 
|--
  “ (lst_size_pre = (Zlength ((strange_output_70 (sorted_l))))) ”
.

Definition strange_sort_list_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_70_pre_z input_l )) (PreH5 : (strange_output_safe_70 input_l )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition strange_sort_list_partial_solve_wit_2_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_70_pre_z input_l )) (PreH6 : (strange_output_safe_70 input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (lst_size_pre >= 0) ” 
  &&  “ (lst_size_pre < INT_MAX) ”
.

Definition strange_sort_list_partial_solve_wit_2_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_70_pre_z input_l )) (PreH6 : (strange_output_safe_70 input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (lst_size_pre >= 0) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition strange_sort_list_partial_solve_wit_2 := strange_sort_list_partial_solve_wit_2_pure -> strange_sort_list_partial_solve_wit_2_aux.

Definition strange_sort_list_partial_solve_wit_3_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_70_pre_z input_l )) (PreH7 : (strange_output_safe_70 input_l )) ,
  ((( &( "sorted" ) )) # Ptr  |->_)
  **  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (lst_size_pre >= 0) ” 
  &&  “ (lst_size_pre < INT_MAX) ”
.

Definition strange_sort_list_partial_solve_wit_3_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_70_pre_z input_l )) (PreH7 : (strange_output_safe_70 input_l )) ,
  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (lst_size_pre >= 0) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ”
  &&  (IntArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition strange_sort_list_partial_solve_wit_3 := strange_sort_list_partial_solve_wit_3_pure -> strange_sort_list_partial_solve_wit_3_aux.

Definition strange_sort_list_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (sublist (0) (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
|--
  “ (i < lst_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (sublist (0) (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (sorted: Z) (data: Z) (out: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (sublist (0) (i) (input_l)) )
  **  (IntArray.undef_seg sorted i lst_size_pre )
|--
  “ (i < lst_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ”
  &&  (((sorted + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg sorted (i + 1 ) lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 i (sublist (0) (i) (input_l)) )
.

Definition strange_sort_list_partial_solve_wit_6_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
|--
  “ (sorted <> 0) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ”
.

Definition strange_sort_list_partial_solve_wit_6_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (problem_70_pre_z input_l )) (PreH8 : (strange_output_safe_70 input_l )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
  **  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
|--
  “ (sorted <> 0) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ”
  &&  (IntArray.seg sorted 0 lst_size_pre input_l )
  **  (IntArray.undef_seg sorted lst_size_pre lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.undef_full data lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_6 := strange_sort_list_partial_solve_wit_6_pure -> strange_sort_list_partial_solve_wit_6_aux.

Definition strange_sort_list_partial_solve_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (k: Z) (right: Z) (left: Z) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) (PreH1 : (left < right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l )) (PreH12 : (Permutation input_l sorted_l )) (PreH13 : (0 <= left)) (PreH14 : (left <= lst_size_pre)) (PreH15 : (right = ((lst_size_pre - 1 ) - left ))) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ (left < right) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= lst_size_pre) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ (k = (2 * left )) ” 
  &&  “ (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left))))) ” 
  &&  “ (k <= lst_size_pre) ”
  &&  (((sorted + (left * sizeof(INT) ) )) # Int  |-> (Znth left sorted_l 0))
  **  (IntArray.missing_i sorted left 0 lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (k: Z) (right: Z) (left: Z) (sorted_l: (@list Z)) (sorted: Z) (data: Z) (out: Z) (PreH1 : (left < right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l )) (PreH12 : (Permutation input_l sorted_l )) (PreH13 : (0 <= left)) (PreH14 : (left <= lst_size_pre)) (PreH15 : (right = ((lst_size_pre - 1 ) - left ))) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.full sorted lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
|--
  “ (left < right) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= lst_size_pre) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ (k = (2 * left )) ” 
  &&  “ (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left))))) ” 
  &&  “ (k <= lst_size_pre) ”
  &&  (((data + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
.

Definition strange_sort_list_partial_solve_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ (k = ((2 * left ) + 1 )) ” 
  &&  “ (k <= lst_size_pre) ”
  &&  (((sorted + (right * sizeof(INT) ) )) # Int  |-> (Znth right sorted_l 0))
  **  (IntArray.missing_i sorted right 0 lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg data k lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (strange_output_safe_70 input_l )) (PreH10 : (sorted_int_list_by 1 sorted_l )) (PreH11 : (Permutation input_l sorted_l )) (PreH12 : (0 <= left)) (PreH13 : (left < right)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (k = ((2 * left ) + 1 ))) (PreH16 : (k <= lst_size_pre)) ,
  (IntArray.full sorted lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg data k lst_size_pre )
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ (k = ((2 * left ) + 1 )) ” 
  &&  “ (k <= lst_size_pre) ”
  &&  (((data + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (k + 1 ) lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (app ((strange_pairs_prefix_70 (sorted_l) (left))) ((cons ((Znth (left) (sorted_l) (0))) ((@nil Z))))) )
.

Definition strange_sort_list_partial_solve_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (left = right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l )) (PreH12 : (Permutation input_l sorted_l )) (PreH13 : (0 <= left)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (left >= right)) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
  **  (IntArray.full sorted lst_size_pre sorted_l )
|--
  “ (left = right) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ (left >= right) ” 
  &&  “ (k = (2 * left )) ” 
  &&  “ (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left))))) ” 
  &&  “ (k <= lst_size_pre) ”
  &&  (((sorted + (left * sizeof(INT) ) )) # Int  |-> (Znth left sorted_l 0))
  **  (IntArray.missing_i sorted left 0 lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
.

Definition strange_sort_list_partial_solve_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (left: Z) (right: Z) (k: Z) (PreH1 : (left = right)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (sorted <> 0)) (PreH5 : (0 <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (lst_size_pre = (Zlength (input_l)))) (PreH8 : (lst_size_pre = (Zlength (sorted_l)))) (PreH9 : (problem_70_pre_z input_l )) (PreH10 : (strange_output_safe_70 input_l )) (PreH11 : (sorted_int_list_by 1 sorted_l )) (PreH12 : (Permutation input_l sorted_l )) (PreH13 : (0 <= left)) (PreH14 : (right = ((lst_size_pre - 1 ) - left ))) (PreH15 : (left >= right)) (PreH16 : (k = (2 * left ))) (PreH17 : (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left)))))) (PreH18 : (k <= lst_size_pre)) ,
  (IntArray.full sorted lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
  **  (IntArray.undef_seg data k lst_size_pre )
|--
  “ (left = right) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (strange_output_safe_70 input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right = ((lst_size_pre - 1 ) - left )) ” 
  &&  “ (left >= right) ” 
  &&  “ (k = (2 * left )) ” 
  &&  “ (k = (Zlength ((strange_pairs_prefix_70 (sorted_l) (left))))) ” 
  &&  “ (k <= lst_size_pre) ”
  &&  (((data + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.full sorted lst_size_pre sorted_l )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.seg data 0 k (strange_pairs_prefix_70 (sorted_l) (left)) )
.

Definition strange_sort_list_partial_solve_wit_13_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (problem_70_spec_z input_l (strange_output_70 (sorted_l)) )) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "sorted" ) )) # Ptr  |-> sorted)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
  **  (IntArray.full_shape sorted lst_size_pre )
|--
  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ”
.

Definition strange_sort_list_partial_solve_wit_13_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (out: Z) (data: Z) (sorted: Z) (PreH1 : (out <> 0)) (PreH2 : (data <> 0)) (PreH3 : (sorted <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (lst_size_pre = (Zlength (input_l)))) (PreH7 : (lst_size_pre = (Zlength (sorted_l)))) (PreH8 : (problem_70_pre_z input_l )) (PreH9 : (problem_70_spec_z input_l (strange_output_70 (sorted_l)) )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
  **  (IntArray.full_shape sorted lst_size_pre )
|--
  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (sorted <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (lst_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_70_pre_z input_l ) ” 
  &&  “ (problem_70_spec_z input_l (strange_output_70 (sorted_l)) ) ”
  &&  (IntArray.full_shape sorted lst_size_pre )
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (IntArray.full data lst_size_pre (strange_output_70 (sorted_l)) )
.

Definition strange_sort_list_partial_solve_wit_13 := strange_sort_list_partial_solve_wit_13_pure -> strange_sort_list_partial_solve_wit_13_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_strange_sort_list_safety_wit_1 : strange_sort_list_safety_wit_1.
Axiom proof_of_strange_sort_list_safety_wit_2 : strange_sort_list_safety_wit_2.
Axiom proof_of_strange_sort_list_safety_wit_3 : strange_sort_list_safety_wit_3.
Axiom proof_of_strange_sort_list_safety_wit_4 : strange_sort_list_safety_wit_4.
Axiom proof_of_strange_sort_list_safety_wit_5 : strange_sort_list_safety_wit_5.
Axiom proof_of_strange_sort_list_safety_wit_6 : strange_sort_list_safety_wit_6.
Axiom proof_of_strange_sort_list_safety_wit_7 : strange_sort_list_safety_wit_7.
Axiom proof_of_strange_sort_list_safety_wit_8 : strange_sort_list_safety_wit_8.
Axiom proof_of_strange_sort_list_safety_wit_9 : strange_sort_list_safety_wit_9.
Axiom proof_of_strange_sort_list_safety_wit_10 : strange_sort_list_safety_wit_10.
Axiom proof_of_strange_sort_list_safety_wit_11 : strange_sort_list_safety_wit_11.
Axiom proof_of_strange_sort_list_safety_wit_12 : strange_sort_list_safety_wit_12.
Axiom proof_of_strange_sort_list_safety_wit_13 : strange_sort_list_safety_wit_13.
Axiom proof_of_strange_sort_list_safety_wit_14 : strange_sort_list_safety_wit_14.
Axiom proof_of_strange_sort_list_entail_wit_1 : strange_sort_list_entail_wit_1.
Axiom proof_of_strange_sort_list_entail_wit_2 : strange_sort_list_entail_wit_2.
Axiom proof_of_strange_sort_list_entail_wit_3 : strange_sort_list_entail_wit_3.
Axiom proof_of_strange_sort_list_entail_wit_4 : strange_sort_list_entail_wit_4.
Axiom proof_of_strange_sort_list_entail_wit_5 : strange_sort_list_entail_wit_5.
Axiom proof_of_strange_sort_list_entail_wit_6 : strange_sort_list_entail_wit_6.
Axiom proof_of_strange_sort_list_entail_wit_7 : strange_sort_list_entail_wit_7.
Axiom proof_of_strange_sort_list_entail_wit_8 : strange_sort_list_entail_wit_8.
Axiom proof_of_strange_sort_list_entail_wit_9_1 : strange_sort_list_entail_wit_9_1.
Axiom proof_of_strange_sort_list_entail_wit_9_2 : strange_sort_list_entail_wit_9_2.
Axiom proof_of_strange_sort_list_entail_wit_10 : strange_sort_list_entail_wit_10.
Axiom proof_of_strange_sort_list_entail_wit_11 : strange_sort_list_entail_wit_11.
Axiom proof_of_strange_sort_list_return_wit_1 : strange_sort_list_return_wit_1.
Axiom proof_of_strange_sort_list_partial_solve_wit_1 : strange_sort_list_partial_solve_wit_1.
Axiom proof_of_strange_sort_list_partial_solve_wit_2_pure : strange_sort_list_partial_solve_wit_2_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_2 : strange_sort_list_partial_solve_wit_2.
Axiom proof_of_strange_sort_list_partial_solve_wit_3_pure : strange_sort_list_partial_solve_wit_3_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_3 : strange_sort_list_partial_solve_wit_3.
Axiom proof_of_strange_sort_list_partial_solve_wit_4 : strange_sort_list_partial_solve_wit_4.
Axiom proof_of_strange_sort_list_partial_solve_wit_5 : strange_sort_list_partial_solve_wit_5.
Axiom proof_of_strange_sort_list_partial_solve_wit_6_pure : strange_sort_list_partial_solve_wit_6_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_6 : strange_sort_list_partial_solve_wit_6.
Axiom proof_of_strange_sort_list_partial_solve_wit_7 : strange_sort_list_partial_solve_wit_7.
Axiom proof_of_strange_sort_list_partial_solve_wit_8 : strange_sort_list_partial_solve_wit_8.
Axiom proof_of_strange_sort_list_partial_solve_wit_9 : strange_sort_list_partial_solve_wit_9.
Axiom proof_of_strange_sort_list_partial_solve_wit_10 : strange_sort_list_partial_solve_wit_10.
Axiom proof_of_strange_sort_list_partial_solve_wit_11 : strange_sort_list_partial_solve_wit_11.
Axiom proof_of_strange_sort_list_partial_solve_wit_12 : strange_sort_list_partial_solve_wit_12.
Axiom proof_of_strange_sort_list_partial_solve_wit_13_pure : strange_sort_list_partial_solve_wit_13_pure.
Axiom proof_of_strange_sort_list_partial_solve_wit_13 : strange_sort_list_partial_solve_wit_13.

End VC_Correct.
