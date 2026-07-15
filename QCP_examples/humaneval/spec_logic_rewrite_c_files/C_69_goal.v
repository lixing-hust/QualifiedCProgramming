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
Require Import coins_69.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function search -----*)

Definition search_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition search_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition search_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "old_max" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "freq" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition search_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "old_max" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "freq" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition search_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "old_max" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "freq" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition search_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "old_max" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "freq" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition search_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "old_max" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "freq" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition search_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  ((( &( "old_max" ) )) # Int  |-> (-1))
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "freq" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition search_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "x" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "freq" ) )) # Int  |-> freq)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "old_max" ) )) # Int  |-> old_max)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition search_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "x" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "freq" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "old_max" ) )) # Int  |-> old_max)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition search_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) = x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq" ) )) # Int  |-> freq)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "old_max" ) )) # Int  |-> old_max)
|--
  “ ((freq + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (freq + 1 )) ”
.

Definition search_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) = x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq" ) )) # Int  |-> freq)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "old_max" ) )) # Int  |-> old_max)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition search_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) = x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq" ) )) # Int  |-> (freq + 1 ))
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "old_max" ) )) # Int  |-> old_max)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition search_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) <> x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "freq" ) )) # Int  |-> freq)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "old_max" ) )) # Int  |-> old_max)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition search_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (old_max: Z) (max: Z) (j: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (freq = (count_z_69 (x) (input_l)))) (PreH10 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH11 : (max = (update_best_69 (old_max) (x) (freq)))) (PreH12 : ((-1) <= max)) (PreH13 : (max <= INT_MAX)) (PreH14 : (max = (find_max_prefix_69 (input_l) ((i + 1 ))))) (PreH15 : (INT_MIN <= x)) (PreH16 : (x <= INT_MAX)) (PreH17 : (INT_MIN <= freq)) (PreH18 : (freq <= INT_MAX)) (PreH19 : (INT_MIN <= j)) (PreH20 : (j <= INT_MAX)) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "freq" ) )) # Int  |-> freq)
  **  ((( &( "old_max" ) )) # Int  |-> old_max)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition search_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ” 
  &&  “ ((-1) = (find_max_prefix_69 (input_l) (0))) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  TT && emp 
|--
  “ ((-1) = (find_max_prefix_69 (input_l) (0))) ”
  &&  emp
).

Definition search_entail_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) ,
  TT && emp 
|--
  “ ((-1) = (find_max_prefix_69 (input_l) (0))) ”
.

Definition search_entail_wit_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ” 
  &&  “ (1 <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (count_prefix_69 ((Znth i input_l 0)) (0) (input_l))) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (count_prefix_69 ((Znth i input_l 0)) (0) (input_l))) ” 
  &&  “ ((Znth i input_l 0) <= INT_MAX) ” 
  &&  “ (1 <= (Znth i input_l 0)) ” 
  &&  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
  &&  emp
).

Definition search_entail_wit_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (count_prefix_69 ((Znth i input_l 0)) (0) (input_l))) ”
.

Definition search_entail_wit_2_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) <= INT_MAX) ”
.

Definition search_entail_wit_2_split_goal_3 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= (Znth i input_l 0)) ”
.

Definition search_entail_wit_2_split_goal_4 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth i input_l 0) = (Znth (i) (input_l) (0))) ”
.

Definition search_entail_wit_3_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) = x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= lst_size_pre) ” 
  &&  “ (0 <= (freq + 1 )) ” 
  &&  “ ((freq + 1 ) <= (j + 1 )) ” 
  &&  “ ((freq + 1 ) = (count_prefix_69 (x) ((j + 1 )) (input_l))) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) = x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ ((freq + 1 ) = (count_prefix_69 (x) ((j + 1 )) (input_l))) ”
  &&  emp
).

Definition search_entail_wit_3_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) = x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ ((freq + 1 ) = (count_prefix_69 (x) ((j + 1 )) (input_l))) ”
.

Definition search_entail_wit_3_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) <> x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= lst_size_pre) ” 
  &&  “ (0 <= freq) ” 
  &&  “ (freq <= (j + 1 )) ” 
  &&  “ (freq = (count_prefix_69 (x) ((j + 1 )) (input_l))) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) <> x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (freq = (count_prefix_69 (x) ((j + 1 )) (input_l))) ”
  &&  emp
).

Definition search_entail_wit_3_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : ((Znth j input_l 0) <> x)) (PreH2 : (j < lst_size_pre)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (0 <= j)) (PreH14 : (j <= lst_size_pre)) (PreH15 : (0 <= freq)) (PreH16 : (freq <= j)) (PreH17 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH18 : ((-1) <= max)) (PreH19 : (max <= INT_MAX)) (PreH20 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (freq = (count_prefix_69 (x) ((j + 1 )) (input_l))) ”
.

Definition search_entail_wit_4 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : (j >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (0 <= j)) (PreH13 : (j <= lst_size_pre)) (PreH14 : (0 <= freq)) (PreH15 : (freq <= j)) (PreH16 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH17 : ((-1) <= max)) (PreH18 : (max <= INT_MAX)) (PreH19 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH20 : (INT_MIN <= old_max)) (PreH21 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (freq = (count_z_69 (x) (input_l))) ” 
  &&  “ (max = max) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= freq) ” 
  &&  “ (freq <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= max) ” 
  &&  “ (max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : (j >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (0 <= j)) (PreH13 : (j <= lst_size_pre)) (PreH14 : (0 <= freq)) (PreH15 : (freq <= j)) (PreH16 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH17 : ((-1) <= max)) (PreH18 : (max <= INT_MAX)) (PreH19 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH20 : (INT_MIN <= old_max)) (PreH21 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (freq = (count_z_69 (x) (input_l))) ”
  &&  emp
).

Definition search_entail_wit_4_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : (j >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (0 <= j)) (PreH13 : (j <= lst_size_pre)) (PreH14 : (0 <= freq)) (PreH15 : (freq <= j)) (PreH16 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH17 : ((-1) <= max)) (PreH18 : (max <= INT_MAX)) (PreH19 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH20 : (INT_MIN <= old_max)) (PreH21 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (freq = (count_z_69 (x) (input_l))) ”
.

Definition search_entail_wit_5_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (freq < x)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (freq = (count_z_69 (x) (input_l)))) (PreH13 : (max = old_max)) (PreH14 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH15 : ((-1) <= old_max)) (PreH16 : (old_max <= INT_MAX)) (PreH17 : (INT_MIN <= x)) (PreH18 : (x <= INT_MAX)) (PreH19 : (INT_MIN <= freq)) (PreH20 : (freq <= INT_MAX)) (PreH21 : (INT_MIN <= j)) (PreH22 : (j <= INT_MAX)) (PreH23 : (INT_MIN <= old_max)) (PreH24 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (freq = (count_z_69 (x) (input_l))) ” 
  &&  “ (old_max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (max = (update_best_69 (old_max) (x) (freq))) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) ((i + 1 )))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= freq) ” 
  &&  “ (freq <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (freq < x)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (freq = (count_z_69 (x) (input_l)))) (PreH13 : (max = old_max)) (PreH14 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH15 : ((-1) <= old_max)) (PreH16 : (old_max <= INT_MAX)) (PreH17 : (INT_MIN <= x)) (PreH18 : (x <= INT_MAX)) (PreH19 : (INT_MIN <= freq)) (PreH20 : (freq <= INT_MAX)) (PreH21 : (INT_MIN <= j)) (PreH22 : (j <= INT_MAX)) (PreH23 : (INT_MIN <= old_max)) (PreH24 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (max = (find_max_prefix_69 (input_l) ((i + 1 )))) ” 
  &&  “ (max = (update_best_69 (old_max) (x) (freq))) ”
  &&  emp
).

Definition search_entail_wit_5_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (freq < x)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (freq = (count_z_69 (x) (input_l)))) (PreH13 : (max = old_max)) (PreH14 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH15 : ((-1) <= old_max)) (PreH16 : (old_max <= INT_MAX)) (PreH17 : (INT_MIN <= x)) (PreH18 : (x <= INT_MAX)) (PreH19 : (INT_MIN <= freq)) (PreH20 : (freq <= INT_MAX)) (PreH21 : (INT_MIN <= j)) (PreH22 : (j <= INT_MAX)) (PreH23 : (INT_MIN <= old_max)) (PreH24 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (max = (find_max_prefix_69 (input_l) ((i + 1 )))) ”
.

Definition search_entail_wit_5_1_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (freq < x)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (freq = (count_z_69 (x) (input_l)))) (PreH13 : (max = old_max)) (PreH14 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH15 : ((-1) <= old_max)) (PreH16 : (old_max <= INT_MAX)) (PreH17 : (INT_MIN <= x)) (PreH18 : (x <= INT_MAX)) (PreH19 : (INT_MIN <= freq)) (PreH20 : (freq <= INT_MAX)) (PreH21 : (INT_MIN <= j)) (PreH22 : (j <= INT_MAX)) (PreH23 : (INT_MIN <= old_max)) (PreH24 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (max = (update_best_69 (old_max) (x) (freq))) ”
.

Definition search_entail_wit_5_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x <= old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (freq = (count_z_69 (x) (input_l))) ” 
  &&  “ (old_max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (max = (update_best_69 (old_max) (x) (freq))) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) ((i + 1 )))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= freq) ” 
  &&  “ (freq <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x <= old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (max = (find_max_prefix_69 (input_l) ((i + 1 )))) ” 
  &&  “ (max = (update_best_69 (old_max) (x) (freq))) ”
  &&  emp
).

Definition search_entail_wit_5_2_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x <= old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (max = (find_max_prefix_69 (input_l) ((i + 1 )))) ”
.

Definition search_entail_wit_5_2_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x <= old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (max = (update_best_69 (old_max) (x) (freq))) ”
.

Definition search_entail_wit_5_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x > old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (freq = (count_z_69 (x) (input_l))) ” 
  &&  “ (old_max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (x = (update_best_69 (old_max) (x) (freq))) ” 
  &&  “ ((-1) <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (x = (find_max_prefix_69 (input_l) ((i + 1 )))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= freq) ” 
  &&  “ (freq <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x > old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (x = (find_max_prefix_69 (input_l) ((i + 1 )))) ” 
  &&  “ (x = (update_best_69 (old_max) (x) (freq))) ”
  &&  emp
).

Definition search_entail_wit_5_3_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x > old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (x = (find_max_prefix_69 (input_l) ((i + 1 )))) ”
.

Definition search_entail_wit_5_3_split_goal_2 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (max: Z) (old_max: Z) (j: Z) (PreH1 : (x > old_max)) (PreH2 : (freq >= x)) (PreH3 : (1 <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (lst_size_pre = (Zlength (input_l)))) (PreH6 : (problem_69_pre_z input_l )) (PreH7 : (list_positive_int_range_69 input_l )) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (x = (Znth (i) (input_l) (0)))) (PreH11 : (1 <= x)) (PreH12 : (x <= INT_MAX)) (PreH13 : (freq = (count_z_69 (x) (input_l)))) (PreH14 : (max = old_max)) (PreH15 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH16 : ((-1) <= old_max)) (PreH17 : (old_max <= INT_MAX)) (PreH18 : (INT_MIN <= x)) (PreH19 : (x <= INT_MAX)) (PreH20 : (INT_MIN <= freq)) (PreH21 : (freq <= INT_MAX)) (PreH22 : (INT_MIN <= j)) (PreH23 : (j <= INT_MAX)) (PreH24 : (INT_MIN <= old_max)) (PreH25 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (x = (update_best_69 (old_max) (x) (freq))) ”
.

Definition search_entail_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (i: Z) (x: Z) (freq: Z) (old_max: Z) (max: Z) (j: Z) (PreH1 : (1 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : (lst_size_pre = (Zlength (input_l)))) (PreH4 : (problem_69_pre_z input_l )) (PreH5 : (list_positive_int_range_69 input_l )) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (x = (Znth (i) (input_l) (0)))) (PreH9 : (freq = (count_z_69 (x) (input_l)))) (PreH10 : (old_max = (find_max_prefix_69 (input_l) (i)))) (PreH11 : (max = (update_best_69 (old_max) (x) (freq)))) (PreH12 : ((-1) <= max)) (PreH13 : (max <= INT_MAX)) (PreH14 : (max = (find_max_prefix_69 (input_l) ((i + 1 ))))) (PreH15 : (INT_MIN <= x)) (PreH16 : (x <= INT_MAX)) (PreH17 : (INT_MIN <= freq)) (PreH18 : (freq <= INT_MAX)) (PreH19 : (INT_MIN <= j)) (PreH20 : (j <= INT_MAX)) (PreH21 : (INT_MIN <= old_max)) (PreH22 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) ((i + 1 )))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= freq) ” 
  &&  “ (freq <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition search_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (problem_69_spec_z input_l max ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
) \/
(
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_69_spec_z input_l max ) ”
  &&  emp
).

Definition search_return_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_69_spec_z input_l max ) ”
.

Definition search_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (j: Z) (freq: Z) (x: Z) (max: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i <= lst_size_pre)) (PreH9 : ((-1) <= max)) (PreH10 : (max <= INT_MAX)) (PreH11 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH12 : (INT_MIN <= x)) (PreH13 : (x <= INT_MAX)) (PreH14 : (INT_MIN <= freq)) (PreH15 : (freq <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (INT_MIN <= old_max)) (PreH19 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (i < lst_size_pre) ” 
  &&  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= freq) ” 
  &&  “ (freq <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition search_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (old_max: Z) (max: Z) (freq: Z) (j: Z) (x: Z) (i: Z) (PreH1 : (j < lst_size_pre)) (PreH2 : (1 <= lst_size_pre)) (PreH3 : (lst_size_pre < INT_MAX)) (PreH4 : (lst_size_pre = (Zlength (input_l)))) (PreH5 : (problem_69_pre_z input_l )) (PreH6 : (list_positive_int_range_69 input_l )) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (x = (Znth (i) (input_l) (0)))) (PreH10 : (1 <= x)) (PreH11 : (x <= INT_MAX)) (PreH12 : (0 <= j)) (PreH13 : (j <= lst_size_pre)) (PreH14 : (0 <= freq)) (PreH15 : (freq <= j)) (PreH16 : (freq = (count_prefix_69 (x) (j) (input_l)))) (PreH17 : ((-1) <= max)) (PreH18 : (max <= INT_MAX)) (PreH19 : (max = (find_max_prefix_69 (input_l) (i)))) (PreH20 : (INT_MIN <= old_max)) (PreH21 : (old_max <= INT_MAX)) ,
  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (j < lst_size_pre) ” 
  &&  “ (1 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_69_pre_z input_l ) ” 
  &&  “ (list_positive_int_range_69 input_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (x = (Znth (i) (input_l) (0))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= lst_size_pre) ” 
  &&  “ (0 <= freq) ” 
  &&  “ (freq <= j) ” 
  &&  “ (freq = (count_prefix_69 (x) (j) (input_l))) ” 
  &&  “ ((-1) <= max) ” 
  &&  “ (max <= INT_MAX) ” 
  &&  “ (max = (find_max_prefix_69 (input_l) (i))) ” 
  &&  “ (INT_MIN <= old_max) ” 
  &&  “ (old_max <= INT_MAX) ”
  &&  (((lst_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j input_l 0))
  **  (IntArray.missing_i lst_pre j 0 lst_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_search_safety_wit_1 : search_safety_wit_1.
Axiom proof_of_search_safety_wit_2 : search_safety_wit_2.
Axiom proof_of_search_safety_wit_3 : search_safety_wit_3.
Axiom proof_of_search_safety_wit_4 : search_safety_wit_4.
Axiom proof_of_search_safety_wit_5 : search_safety_wit_5.
Axiom proof_of_search_safety_wit_6 : search_safety_wit_6.
Axiom proof_of_search_safety_wit_7 : search_safety_wit_7.
Axiom proof_of_search_safety_wit_8 : search_safety_wit_8.
Axiom proof_of_search_safety_wit_9 : search_safety_wit_9.
Axiom proof_of_search_safety_wit_10 : search_safety_wit_10.
Axiom proof_of_search_safety_wit_11 : search_safety_wit_11.
Axiom proof_of_search_safety_wit_12 : search_safety_wit_12.
Axiom proof_of_search_safety_wit_13 : search_safety_wit_13.
Axiom proof_of_search_safety_wit_14 : search_safety_wit_14.
Axiom proof_of_search_safety_wit_15 : search_safety_wit_15.
Axiom proof_of_search_entail_wit_1 : search_entail_wit_1.
Axiom proof_of_search_entail_wit_2 : search_entail_wit_2.
Axiom proof_of_search_entail_wit_3_1 : search_entail_wit_3_1.
Axiom proof_of_search_entail_wit_3_2 : search_entail_wit_3_2.
Axiom proof_of_search_entail_wit_4 : search_entail_wit_4.
Axiom proof_of_search_entail_wit_5_1 : search_entail_wit_5_1.
Axiom proof_of_search_entail_wit_5_2 : search_entail_wit_5_2.
Axiom proof_of_search_entail_wit_5_3 : search_entail_wit_5_3.
Axiom proof_of_search_entail_wit_6 : search_entail_wit_6.
Axiom proof_of_search_return_wit_1 : search_return_wit_1.
Axiom proof_of_search_partial_solve_wit_1 : search_partial_solve_wit_1.
Axiom proof_of_search_partial_solve_wit_2 : search_partial_solve_wit_2.

End VC_Correct.
