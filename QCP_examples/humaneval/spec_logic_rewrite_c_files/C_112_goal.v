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
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.coins_112.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function reverse_delete -----*)

Definition reverse_delete_safety_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (s_pre = s0)) (PreH5 : (c_pre = c0)) (PreH6 : (valid_string input )) (PreH7 : (valid_string removed )) (PreH8 : (problem_112_pre_z input removed )) (PreH9 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH10 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (c_pre = c0)) (PreH7 : (valid_string input )) (PreH8 : (valid_string removed )) (PreH9 : (problem_112_pre_z input removed )) (PreH10 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (removed)) < INT_MAX)) ,
  (PtrArray.undef_seg retval_2 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (string_length (input)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (removed)) + 1 ))) (PreH5 : (0 <= ((string_length (input)) + 1 ))) (PreH6 : (s_pre = s0)) (PreH7 : (c_pre = c0)) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval_3)
  **  (PtrArray.undef_seg retval_2 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_4 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= ((string_length (removed)) + 1 ))) (PreH5 : (0 <= ((string_length (input)) + 1 ))) (PreH6 : (s_pre = s0)) (PreH7 : (c_pre = c0)) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  (PtrArray.undef_seg retval_3 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition reverse_delete_safety_wit_5 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (string_length (input)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (removed)) + 1 ))) (PreH5 : (0 <= ((string_length (input)) + 1 ))) (PreH6 : (s_pre = s0)) (PreH7 : (c_pre = c0)) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval_3)
  **  (PtrArray.undef_seg retval_2 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_6 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 = (string_length (input)))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= ((string_length (removed)) + 1 ))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (s_pre = s0)) (PreH8 : (c_pre = c0)) (PreH9 : (valid_string input )) (PreH10 : (valid_string removed )) (PreH11 : (problem_112_pre_z input removed )) (PreH12 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "filtered" ) )) # Ptr  |-> retval_4)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval_3)
  **  (PtrArray.undef_seg retval_2 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_7 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (strchr_result removed ch retval c0 )) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (valid_string input )) (PreH17 : (valid_string removed )) (PreH18 : (problem_112_pre_z input removed )) (PreH19 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH20 : ((string_length (removed)) < INT_MAX)) (PreH21 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (store_string c0 removed )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "hit" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_8 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "hit" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition reverse_delete_safety_wit_9 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "hit" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_10 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_11 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (store_string c0 removed )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_12 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = (Zlength (filtered_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (filter_prefix_state_112 input removed i filtered_l )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_13 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (i: Z) (k: Z) (m: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= m)) (PreH6 : (m <= n)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (filtered <> 0)) (PreH10 : (valid_string input )) (PreH11 : (valid_string removed )) (PreH12 : (problem_112_pre_z input removed )) (PreH13 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "pal" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_14 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (i: Z) (k: Z) (m: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= m)) (PreH6 : (m <= n)) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_15 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (filtered <> 0)) (PreH10 : (valid_string input )) (PreH11 : (valid_string removed )) (PreH12 : (problem_112_pre_z input removed )) (PreH13 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (removed)) < INT_MAX)) (PreH15 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition reverse_delete_safety_wit_16 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (filtered <> 0)) (PreH10 : (valid_string input )) (PreH11 : (valid_string removed )) (PreH12 : (problem_112_pre_z input removed )) (PreH13 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (removed)) < INT_MAX)) (PreH15 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition reverse_delete_safety_wit_17 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (filtered <> 0)) (PreH10 : (valid_string input )) (PreH11 : (valid_string removed )) (PreH12 : (problem_112_pre_z input removed )) (PreH13 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (removed)) < INT_MAX)) (PreH15 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_18 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (filtered <> 0)) (PreH10 : (valid_string input )) (PreH11 : (valid_string removed )) (PreH12 : (problem_112_pre_z input removed )) (PreH13 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (removed)) < INT_MAX)) (PreH15 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_19 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (((m - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((m - 1 ) - i )) ”
) \/
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (((m - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((m - 1 ) - i )) ”
).

Definition reverse_delete_safety_wit_19_split_goal_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (((m - 1 ) - i ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_19_split_goal_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((INT_MIN) <= ((m - 1 ) - i )) ”
.

Definition reverse_delete_safety_wit_20 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (((m - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((m - 1 ) - i )) ”
) \/
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (((m - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((m - 1 ) - i )) ”
).

Definition reverse_delete_safety_wit_20_split_goal_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (((m - 1 ) - i ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_20_split_goal_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((INT_MIN) <= ((m - 1 ) - i )) ”
.

Definition reverse_delete_safety_wit_21 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m - 1 )) ”
) \/
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m - 1 )) ”
).

Definition reverse_delete_safety_wit_21_split_goal_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m - 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_21_split_goal_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((INT_MIN) <= (m - 1 )) ”
.

Definition reverse_delete_safety_wit_22 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m - 1 )) ”
) \/
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m - 1 )) ”
).

Definition reverse_delete_safety_wit_22_split_goal_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((m - 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_22_split_goal_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((INT_MIN) <= (m - 1 )) ”
.

Definition reverse_delete_safety_wit_23 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_24 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i < (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_25 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 1)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_26 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_27 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 1)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 1)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition reverse_delete_safety_wit_27_split_goal_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 1)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_27_split_goal_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 1)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_28 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition reverse_delete_safety_wit_28_split_goal_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_28_split_goal_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_29 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal = 0)) ,
  ((( &( "flag" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ False ”
.

Definition reverse_delete_safety_wit_30 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal <> 0)) ,
  ((( &( "flag" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ False ”
.

Definition reverse_delete_safety_wit_31 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal <> 0)) ,
  ((( &( "flag" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition reverse_delete_safety_wit_32 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_full retval 5 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_33 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_full retval 5 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (84 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 84) ”
.

Definition reverse_delete_safety_wit_34 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (0 + 1 ) 5 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_35 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (0 + 1 ) 5 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (114 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 114) ”
.

Definition reverse_delete_safety_wit_36 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_37 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition reverse_delete_safety_wit_38 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (2 + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition reverse_delete_safety_wit_39 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (2 + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition reverse_delete_safety_wit_40 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (3 + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition reverse_delete_safety_wit_41 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (3 + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_42 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal = 0)) ,
  ((( &( "flag" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition reverse_delete_safety_wit_43 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_full retval 6 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_44 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_full retval 6 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (70 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 70) ”
.

Definition reverse_delete_safety_wit_45 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_46 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition reverse_delete_safety_wit_47 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_48 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (108 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 108) ”
.

Definition reverse_delete_safety_wit_49 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition reverse_delete_safety_wit_50 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (115 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 115) ”
.

Definition reverse_delete_safety_wit_51 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition reverse_delete_safety_wit_52 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition reverse_delete_safety_wit_53 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition reverse_delete_safety_wit_54 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_55 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (4 + 1 ) 5 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_56 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (5 + 1 ) 6 )
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_57 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_seg data (0 + 1 ) 2 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_58 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_seg data (0 + 1 ) 2 )
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((( &( "flag" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_entail_wit_1 := 
(
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 = (string_length (input)))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= ((string_length (removed)) + 1 ))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (s_pre = s0)) (PreH8 : (c_pre = c0)) (PreH9 : (valid_string input )) (PreH10 : (valid_string removed )) (PreH11 : (problem_112_pre_z input removed )) (PreH12 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (PtrArray.undef_seg retval_2 0 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  EX (filtered_l: (@list Z)) ,
  “ (retval_3 = (string_length (input))) ” 
  &&  “ (0 = (Zlength (filtered_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_112 input removed 0 filtered_l ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg retval_2 0 2 )
  **  (CharArray.full retval_4 0 filtered_l )
  **  (CharArray.undef_seg retval_4 0 (retval_3 + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
) \/
(
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 = (string_length (input)))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= ((string_length (removed)) + 1 ))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (s_pre = s0)) (PreH8 : (c_pre = c0)) (PreH9 : (valid_string input )) (PreH10 : (valid_string removed )) (PreH11 : (problem_112_pre_z input removed )) (PreH12 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
|--
  “ (filter_prefix_state_112 input removed 0 (@nil Z) ) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
).

Definition reverse_delete_entail_wit_1_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 = (string_length (input)))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= ((string_length (removed)) + 1 ))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (s_pre = s0)) (PreH8 : (c_pre = c0)) (PreH9 : (valid_string input )) (PreH10 : (valid_string removed )) (PreH11 : (problem_112_pre_z input removed )) (PreH12 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
|--
  “ (filter_prefix_state_112 input removed 0 (@nil Z) ) ”
.

Definition reverse_delete_entail_wit_1_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 = (string_length (input)))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= ((string_length (removed)) + 1 ))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (s_pre = s0)) (PreH8 : (c_pre = c0)) (PreH9 : (valid_string input )) (PreH10 : (valid_string removed )) (PreH11 : (problem_112_pre_z input removed )) (PreH12 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
|--
  “ (0 <= retval_3) ”
.

Definition reverse_delete_entail_wit_1_split_goal_3 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 = (string_length (input)))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= ((string_length (removed)) + 1 ))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (s_pre = s0)) (PreH8 : (c_pre = c0)) (PreH9 : (valid_string input )) (PreH10 : (valid_string removed )) (PreH11 : (problem_112_pre_z input removed )) (PreH12 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition reverse_delete_entail_wit_1_split_goal_spatial := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 = (string_length (input)))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= ((string_length (removed)) + 1 ))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (s_pre = s0)) (PreH8 : (c_pre = c0)) (PreH9 : (valid_string input )) (PreH10 : (valid_string removed )) (PreH11 : (problem_112_pre_z input removed )) (PreH12 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
|--
  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_full retval_4 (retval_3 + 1 ) )
.

Definition reverse_delete_entail_wit_2 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = (Zlength (filtered_l_2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l_2 )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Znth i (c_string (input)) 0) = (Znth (i) ((c_string (input))) (0))) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 127) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_112 input removed i filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
) \/
(
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (k = (Zlength (filtered_l_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (filtered <> 0)) (PreH13 : (valid_string input )) (PreH14 : (valid_string removed )) (PreH15 : (problem_112_pre_z input removed )) (PreH16 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (removed)) < INT_MAX)) (PreH18 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (input)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) = (Znth (i) ((c_string (input))) (0))) ”
  &&  emp
).

Definition reverse_delete_entail_wit_2_split_goal_1 := 
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (k = (Zlength (filtered_l_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (filtered <> 0)) (PreH13 : (valid_string input )) (PreH14 : (valid_string removed )) (PreH15 : (problem_112_pre_z input removed )) (PreH16 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (removed)) < INT_MAX)) (PreH18 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (input)) 0) <= 127) ”
.

Definition reverse_delete_entail_wit_2_split_goal_2 := 
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (k = (Zlength (filtered_l_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (filtered <> 0)) (PreH13 : (valid_string input )) (PreH14 : (valid_string removed )) (PreH15 : (problem_112_pre_z input removed )) (PreH16 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (removed)) < INT_MAX)) (PreH18 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ (0 <= (Znth i (c_string (input)) 0)) ”
.

Definition reverse_delete_entail_wit_2_split_goal_3 := 
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (k = (Zlength (filtered_l_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (filtered <> 0)) (PreH13 : (valid_string input )) (PreH14 : (valid_string removed )) (PreH15 : (problem_112_pre_z input removed )) (PreH16 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (removed)) < INT_MAX)) (PreH18 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (input)) 0) = (Znth (i) ((c_string (input))) (0))) ”
.

Definition reverse_delete_entail_wit_3_1 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l_2) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ ((k + 1 ) = (Zlength (filtered_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_112 input removed (i + 1 ) filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered (k + 1 ) filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
) \/
(
forall (c0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ (filter_prefix_state_112 input removed (i + 1 ) (app (filtered_l_2) ((cons (ch) ((@nil Z))))) ) ” 
  &&  “ ((k + 1 ) = (Zlength ((app (filtered_l_2) ((cons (ch) ((@nil Z)))))))) ”
  &&  emp
).

Definition reverse_delete_entail_wit_3_1_split_goal_1 := 
forall (c0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ (filter_prefix_state_112 input removed (i + 1 ) (app (filtered_l_2) ((cons (ch) ((@nil Z))))) ) ”
.

Definition reverse_delete_entail_wit_3_1_split_goal_2 := 
forall (c0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ ((k + 1 ) = (Zlength ((app (filtered_l_2) ((cons (ch) ((@nil Z)))))))) ”
.

Definition reverse_delete_entail_wit_3_2 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  (store_string c0 removed )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l_2 )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
|--
  EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (i + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_112 input removed (i + 1 ) filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
) \/
(
forall (c0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ (filter_prefix_state_112 input removed (i + 1 ) filtered_l_2 ) ”
  &&  emp
).

Definition reverse_delete_entail_wit_3_2_split_goal_1 := 
forall (c0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l_2 )) ,
  TT && emp 
|--
  “ (filter_prefix_state_112 input removed (i + 1 ) filtered_l_2 ) ”
.

Definition reverse_delete_entail_wit_4 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (filtered <> 0)) (PreH13 : (valid_string input )) (PreH14 : (valid_string removed )) (PreH15 : (problem_112_pre_z input removed )) (PreH16 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (removed)) < INT_MAX)) (PreH18 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (k = k) ” 
  &&  “ (k = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
) \/
(
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (filtered <> 0)) (PreH14 : (valid_string input )) (PreH15 : (valid_string removed )) (PreH16 : (problem_112_pre_z input removed )) (PreH17 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (removed)) < INT_MAX)) (PreH19 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons (0) ((@nil Z))))) )
|--
  “ (k = (Zlength ((filter_not_in_z_112 (input) (removed))))) ”
  &&  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
).

Definition reverse_delete_entail_wit_4_split_goal_1 := 
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (filtered <> 0)) (PreH14 : (valid_string input )) (PreH15 : (valid_string removed )) (PreH16 : (problem_112_pre_z input removed )) (PreH17 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (removed)) < INT_MAX)) (PreH19 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons (0) ((@nil Z))))) )
|--
  “ (k = (Zlength ((filter_not_in_z_112 (input) (removed))))) ”
.

Definition reverse_delete_entail_wit_4_split_goal_spatial := 
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (filtered <> 0)) (PreH14 : (valid_string input )) (PreH15 : (valid_string removed )) (PreH16 : (problem_112_pre_z input removed )) (PreH17 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (removed)) < INT_MAX)) (PreH19 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
.

Definition reverse_delete_entail_wit_5 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (i: Z) (k: Z) (m: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= m)) (PreH6 : (m <= n)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (filtered <> 0)) (PreH10 : (valid_string input )) (PreH11 : (valid_string removed )) (PreH12 : (problem_112_pre_z input removed )) (PreH13 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (removed)) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= n) ” 
  &&  “ (1 = 1) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
.

Definition reverse_delete_entail_wit_6 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (i: Z) (k: Z) (m: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= m)) (PreH6 : (m <= n)) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) 0 pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) 0 pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_entail_wit_7_1 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (m ÷ 2 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) 0 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
) \/
(
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH4 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH5 : (i < (m ÷ 2 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (k = m)) (PreH8 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= (m ÷ 2 ))) (PreH11 : (pal = 0)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (filtered <> 0)) (PreH15 : (valid_string input )) (PreH16 : (valid_string removed )) (PreH17 : (problem_112_pre_z input removed )) (PreH18 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (removed)) < INT_MAX)) (PreH20 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  TT && emp 
|--
  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) 0 ) ”
  &&  emp
).

Definition reverse_delete_entail_wit_7_1_split_goal_1 := 
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH4 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH5 : (i < (m ÷ 2 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (k = m)) (PreH8 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= (m ÷ 2 ))) (PreH11 : (pal = 0)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (filtered <> 0)) (PreH15 : (valid_string input )) (PreH16 : (valid_string removed )) (PreH17 : (problem_112_pre_z input removed )) (PreH18 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (removed)) < INT_MAX)) (PreH20 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  TT && emp 
|--
  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) 0 ) ”
.

Definition reverse_delete_entail_wit_7_2 := 
(
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 1)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (m ÷ 2 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) 0 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
) \/
(
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH4 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH5 : (i < (m ÷ 2 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (k = m)) (PreH8 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= (m ÷ 2 ))) (PreH11 : (pal = 1)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (filtered <> 0)) (PreH15 : (valid_string input )) (PreH16 : (valid_string removed )) (PreH17 : (problem_112_pre_z input removed )) (PreH18 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (removed)) < INT_MAX)) (PreH20 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  TT && emp 
|--
  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) 0 ) ”
  &&  emp
).

Definition reverse_delete_entail_wit_7_2_split_goal_1 := 
forall (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (0 <= ((string_length (removed)) + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH4 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) <> (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH5 : (i < (m ÷ 2 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (k = m)) (PreH8 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= (m ÷ 2 ))) (PreH11 : (pal = 1)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (filtered <> 0)) (PreH15 : (valid_string input )) (PreH16 : (valid_string removed )) (PreH17 : (problem_112_pre_z input removed )) (PreH18 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (removed)) < INT_MAX)) (PreH20 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  TT && emp 
|--
  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) 0 ) ”
.

Definition reverse_delete_entail_wit_8_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 1)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_entail_wit_8_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : ((Znth i (c_string ((filter_not_in_z_112 (input) (removed)))) 0) = (Znth ((m - 1 ) - i ) (c_string ((filter_not_in_z_112 (input) (removed)))) 0))) (PreH2 : (i < (m ÷ 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (k = m)) (PreH5 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH6 : (0 <= i)) (PreH7 : (i <= (m ÷ 2 ))) (PreH8 : (pal = 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (filtered <> 0)) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_entail_wit_9_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i < (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (filtered <> 0)) (PreH10 : (valid_string input )) (PreH11 : (valid_string removed )) (PreH12 : (problem_112_pre_z input removed )) (PreH13 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (removed)) < INT_MAX)) (PreH15 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) (i + 1 ) pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_entail_wit_9_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i >= (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_entail_wit_9_3 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (pal: Z) (i: Z) (m: Z) (k: Z) (n: Z) (PreH1 : (i >= (m ÷ 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = m)) (PreH4 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH5 : (0 <= i)) (PreH6 : (i <= (m ÷ 2 ))) (PreH7 : (pal = 1)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (palindrome_scan_state_112 (filter_not_in_z_112 (input) (removed)) i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_entail_wit_10_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal = 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
.

Definition reverse_delete_entail_wit_10_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal = 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
.

Definition reverse_delete_entail_wit_11_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
.

Definition reverse_delete_entail_wit_11_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
.

Definition reverse_delete_return_wit_1 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal_2: Z) (out: Z) (data_2: Z) (filtered_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal_2 = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal_2 )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data_2 <> 0)) (PreH19 : (filtered_2 <> 0)) (PreH20 : (pal_2 <> 0)) ,
  (((data_2 + (1 * sizeof(PTR) ) )) # Ptr  |-> retval)
  **  (PtrArray.undef_missing_i data_2 1 (0 + 1 ) 2 )
  **  (((data_2 + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered_2)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered_2 ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered_2 (m + 1 ) (n + 1 ) )
|--
  (EX (filtered_l: (@list Z))  (pal: Z)  (flag: Z)  (filtered: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (flag <> 0) ” 
  &&  “ (pal = 1) ” 
  &&  “ (problem_112_spec_z input removed filtered_l pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.full data 2 (cons (filtered) ((cons (flag) ((@nil Z))))) )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered ((Zlength (filtered_l)) + 1 ) ((string_length (input)) + 1 ) )
  **  (store_string flag (flag_payload_112 (pal)) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (EX (filtered_l: (@list Z))  (pal: Z)  (flag: Z)  (filtered: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (flag <> 0) ” 
  &&  “ (pal = 0) ” 
  &&  “ (problem_112_spec_z input removed filtered_l pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.full data 2 (cons (filtered) ((cons (flag) ((@nil Z))))) )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered ((Zlength (filtered_l)) + 1 ) ((string_length (input)) + 1 ) )
  **  (store_string flag (flag_payload_112 (pal)) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_return_wit_2 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal_2: Z) (out: Z) (data_2: Z) (filtered_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal_2 = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal_2 )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data_2 <> 0)) (PreH19 : (filtered_2 <> 0)) (PreH20 : (pal_2 = 0)) ,
  (((data_2 + (1 * sizeof(PTR) ) )) # Ptr  |-> retval)
  **  (PtrArray.undef_missing_i data_2 1 (0 + 1 ) 2 )
  **  (((data_2 + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered_2)
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered_2 ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered_2 (m + 1 ) (n + 1 ) )
|--
  (EX (filtered_l: (@list Z))  (pal: Z)  (flag: Z)  (filtered: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (flag <> 0) ” 
  &&  “ (pal = 1) ” 
  &&  “ (problem_112_spec_z input removed filtered_l pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.full data 2 (cons (filtered) ((cons (flag) ((@nil Z))))) )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered ((Zlength (filtered_l)) + 1 ) ((string_length (input)) + 1 ) )
  **  (store_string flag (flag_payload_112 (pal)) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
  ||
  (EX (filtered_l: (@list Z))  (pal: Z)  (flag: Z)  (filtered: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (flag <> 0) ” 
  &&  “ (pal = 0) ” 
  &&  “ (problem_112_spec_z input removed filtered_l pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.full data 2 (cons (filtered) ((cons (flag) ((@nil Z))))) )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered ((Zlength (filtered_l)) + 1 ) ((string_length (input)) + 1 ) )
  **  (store_string flag (flag_payload_112 (pal)) )
  **  (store_string s0 input )
  **  (store_string c0 removed ))
.

Definition reverse_delete_partial_solve_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (PreH1 : (s_pre = s0)) (PreH2 : (c_pre = c0)) (PreH3 : (valid_string input )) (PreH4 : (valid_string removed )) (PreH5 : (problem_112_pre_z input removed )) (PreH6 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH7 : ((string_length (removed)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (store_string c_pre removed )
|--
  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (c_pre = c0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ”
  &&  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition reverse_delete_partial_solve_wit_2_pure := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (s_pre = s0)) (PreH5 : (c_pre = c0)) (PreH6 : (valid_string input )) (PreH7 : (valid_string removed )) (PreH8 : (problem_112_pre_z input removed )) (PreH9 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH10 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= 2) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition reverse_delete_partial_solve_wit_2_aux := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (s_pre = s0)) (PreH5 : (c_pre = c0)) (PreH6 : (valid_string input )) (PreH7 : (valid_string removed )) (PreH8 : (problem_112_pre_z input removed )) (PreH9 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH10 : ((string_length (removed)) < INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (0 <= 2) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (c_pre = c0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition reverse_delete_partial_solve_wit_2 := reverse_delete_partial_solve_wit_2_pure -> reverse_delete_partial_solve_wit_2_aux.

Definition reverse_delete_partial_solve_wit_3_pure := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (c_pre = c0)) (PreH7 : (valid_string input )) (PreH8 : (valid_string removed )) (PreH9 : (problem_112_pre_z input removed )) (PreH10 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  (PtrArray.undef_seg retval_2 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition reverse_delete_partial_solve_wit_3_aux := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (c_pre = c0)) (PreH7 : (valid_string input )) (PreH8 : (valid_string removed )) (PreH9 : (problem_112_pre_z input removed )) (PreH10 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (removed)) < INT_MAX)) ,
  (PtrArray.undef_seg retval_2 0 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (c_pre = c0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (PtrArray.undef_seg retval_2 0 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
.

Definition reverse_delete_partial_solve_wit_3 := reverse_delete_partial_solve_wit_3_pure -> reverse_delete_partial_solve_wit_3_aux.

Definition reverse_delete_partial_solve_wit_4_pure := 
(
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= ((string_length (removed)) + 1 ))) (PreH5 : (0 <= ((string_length (input)) + 1 ))) (PreH6 : (s_pre = s0)) (PreH7 : (c_pre = c0)) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) ,
  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  (PtrArray.undef_seg retval_3 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (2 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (retval = (string_length (input)))) (PreH8 : (retval_3 <> 0)) (PreH9 : (retval_2 <> 0)) (PreH10 : (0 <= ((string_length (removed)) + 1 ))) (PreH11 : (0 <= ((string_length (input)) + 1 ))) (PreH12 : (s_pre = s0)) (PreH13 : (c_pre = c0)) (PreH14 : (valid_string input )) (PreH15 : (valid_string removed )) (PreH16 : (problem_112_pre_z input removed )) (PreH17 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  (PtrArray.undef_seg retval_3 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 < (retval + 1 )) ”
).

Definition reverse_delete_partial_solve_wit_4_pure_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (2 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (retval = (string_length (input)))) (PreH8 : (retval_3 <> 0)) (PreH9 : (retval_2 <> 0)) (PreH10 : (0 <= ((string_length (removed)) + 1 ))) (PreH11 : (0 <= ((string_length (input)) + 1 ))) (PreH12 : (s_pre = s0)) (PreH13 : (c_pre = c0)) (PreH14 : (valid_string input )) (PreH15 : (valid_string removed )) (PreH16 : (problem_112_pre_z input removed )) (PreH17 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (removed)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  (PtrArray.undef_seg retval_3 0 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 < (retval + 1 )) ”
.

Definition reverse_delete_partial_solve_wit_4_aux := 
forall (c_pre: Z) (s_pre: Z) (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= ((string_length (removed)) + 1 ))) (PreH5 : (0 <= ((string_length (input)) + 1 ))) (PreH6 : (s_pre = s0)) (PreH7 : (c_pre = c0)) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (PtrArray.undef_seg retval_3 0 2 )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (c_pre = c0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (PtrArray.undef_seg retval_3 0 2 )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full c_pre ((string_length (removed)) + 1 ) (c_string (removed)) )
.

Definition reverse_delete_partial_solve_wit_4 := reverse_delete_partial_solve_wit_4_pure -> reverse_delete_partial_solve_wit_4_aux.

Definition reverse_delete_partial_solve_wit_5_pure := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (filtered <> 0)) (PreH13 : (valid_string input )) (PreH14 : (valid_string removed )) (PreH15 : (problem_112_pre_z input removed )) (PreH16 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (removed)) < INT_MAX)) (PreH18 : (filter_prefix_state_112 input removed i filtered_l )) ,
  ((( &( "hit" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (valid_string removed ) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ”
.

Definition reverse_delete_partial_solve_wit_5_aux := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (filtered <> 0)) (PreH13 : (valid_string input )) (PreH14 : (valid_string removed )) (PreH15 : (problem_112_pre_z input removed )) (PreH16 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (removed)) < INT_MAX)) (PreH18 : (filter_prefix_state_112 input removed i filtered_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (valid_string removed ) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ (ch = (Znth (i) ((c_string (input))) (0))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_112 input removed i filtered_l ) ”
  &&  (store_string c0 removed )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_5 := reverse_delete_partial_solve_wit_5_pure -> reverse_delete_partial_solve_wit_5_aux.

Definition reverse_delete_partial_solve_wit_6 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (ch: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result removed ch retval c0 )) (PreH3 : (0 <= ((string_length (removed)) + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (ch = (Znth (i) ((c_string (input))) (0)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (filtered <> 0)) (PreH17 : (valid_string input )) (PreH18 : (valid_string removed )) (PreH19 : (problem_112_pre_z input removed )) (PreH20 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (removed)) < INT_MAX)) (PreH22 : (filter_prefix_state_112 input removed i filtered_l )) ,
  (store_string c0 removed )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
|--
  “ (retval = 0) ” 
  &&  “ (strchr_result removed ch retval c0 ) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ (ch = (Znth (i) ((c_string (input))) (0))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_112 input removed i filtered_l ) ”
  &&  (((filtered + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.undef_missing_i filtered k k (n + 1 ) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
.

Definition reverse_delete_partial_solve_wit_7 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (filtered: Z) (data: Z) (out: Z) (i: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (k = (Zlength (filtered_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (filtered <> 0)) (PreH11 : (valid_string input )) (PreH12 : (valid_string removed )) (PreH13 : (problem_112_pre_z input removed )) (PreH14 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH15 : ((string_length (removed)) < INT_MAX)) (PreH16 : (filter_prefix_state_112 input removed i filtered_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i >= n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_112 input removed i filtered_l ) ”
  &&  (((filtered + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i filtered k k (n + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.full filtered k filtered_l )
.

Definition reverse_delete_partial_solve_wit_8_pure := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal <> 0)) ,
  ((( &( "flag" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 < 5) ” 
  &&  “ (5 < INT_MAX) ”
.

Definition reverse_delete_partial_solve_wit_8_aux := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 1)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 < 5) ” 
  &&  “ (5 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_8 := reverse_delete_partial_solve_wit_8_pure -> reverse_delete_partial_solve_wit_8_aux.

Definition reverse_delete_partial_solve_wit_9 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_full retval 5 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 5 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_10 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (0 + 1 ) 5 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 5 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_11 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (((retval + (2 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 2 (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_12 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (2 + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (((retval + (3 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 3 (2 + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_13 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (3 + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (((retval + (4 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 4 (3 + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_14_pure := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal = 0)) ,
  ((( &( "flag" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "c" ) )) # Ptr  |-> c0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 < 6) ” 
  &&  “ (6 < INT_MAX) ”
.

Definition reverse_delete_partial_solve_wit_14_aux := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (k = m)) (PreH3 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH4 : (0 <= i)) (PreH5 : (i <= (m ÷ 2 ))) (PreH6 : (pal = 0)) (PreH7 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH8 : (valid_string input )) (PreH9 : (valid_string removed )) (PreH10 : (problem_112_pre_z input removed )) (PreH11 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH12 : ((string_length (removed)) < INT_MAX)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (filtered <> 0)) (PreH16 : (pal = 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (store_string filtered (filter_not_in_z_112 (input) (removed)) )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
  **  (store_string s0 input )
  **  (store_string c0 removed )
|--
  “ (0 < 6) ” 
  &&  “ (6 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_14 := reverse_delete_partial_solve_wit_14_pure -> reverse_delete_partial_solve_wit_14_aux.

Definition reverse_delete_partial_solve_wit_15 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_full retval 6 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 6 )
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_16 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_17 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((retval + (2 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 2 (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_18 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((retval + (3 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 3 (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_19 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((retval + (4 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 4 (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_20 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((retval + (5 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 5 (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_21 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (CharArray.undef_seg retval (4 + 1 ) 5 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (((data + (0 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (0 + 1 ) 2 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_22 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (CharArray.undef_seg retval (5 + 1 ) 6 )
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_seg data 0 2 )
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((data + (0 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (0 + 1 ) 2 )
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_23 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 1)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal <> 0)) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_seg data (0 + 1 ) 2 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 1) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal <> 0) ”
  &&  (((data + (1 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data 1 (0 + 1 ) 2 )
  **  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 117)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 114)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 84)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_24 := 
forall (c0: Z) (s0: Z) (removed: (@list Z)) (input: (@list Z)) (n: Z) (k: Z) (m: Z) (i: Z) (pal: Z) (out: Z) (data: Z) (filtered: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (removed)) + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (k = m)) (PreH7 : (m = (Zlength ((filter_not_in_z_112 (input) (removed)))))) (PreH8 : (0 <= i)) (PreH9 : (i <= (m ÷ 2 ))) (PreH10 : (pal = 0)) (PreH11 : (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal )) (PreH12 : (valid_string input )) (PreH13 : (valid_string removed )) (PreH14 : (problem_112_pre_z input removed )) (PreH15 : (((string_length (input)) + 2 ) < INT_MAX)) (PreH16 : ((string_length (removed)) < INT_MAX)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (filtered <> 0)) (PreH20 : (pal = 0)) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_seg data (0 + 1 ) 2 )
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (removed)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (k = m) ” 
  &&  “ (m = (Zlength ((filter_not_in_z_112 (input) (removed))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (m ÷ 2 )) ” 
  &&  “ (pal = 0) ” 
  &&  “ (palindrome_result_112 (filter_not_in_z_112 (input) (removed)) pal ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string removed ) ” 
  &&  “ (problem_112_pre_z input removed ) ” 
  &&  “ (((string_length (input)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (removed)) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (pal = 0) ”
  &&  (((data + (1 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data 1 (0 + 1 ) 2 )
  **  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 101)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 115)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 108)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 97)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 70)
  **  (CharArray.full c0 ((string_length (removed)) + 1 ) (c_string (removed)) )
  **  (CharArray.full s0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full filtered ((string_length ((filter_not_in_z_112 (input) (removed)))) + 1 ) (c_string ((filter_not_in_z_112 (input) (removed)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (m + 1 ) (n + 1 ) )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_reverse_delete_safety_wit_1 : reverse_delete_safety_wit_1.
Axiom proof_of_reverse_delete_safety_wit_2 : reverse_delete_safety_wit_2.
Axiom proof_of_reverse_delete_safety_wit_3 : reverse_delete_safety_wit_3.
Axiom proof_of_reverse_delete_safety_wit_4 : reverse_delete_safety_wit_4.
Axiom proof_of_reverse_delete_safety_wit_5 : reverse_delete_safety_wit_5.
Axiom proof_of_reverse_delete_safety_wit_6 : reverse_delete_safety_wit_6.
Axiom proof_of_reverse_delete_safety_wit_7 : reverse_delete_safety_wit_7.
Axiom proof_of_reverse_delete_safety_wit_8 : reverse_delete_safety_wit_8.
Axiom proof_of_reverse_delete_safety_wit_9 : reverse_delete_safety_wit_9.
Axiom proof_of_reverse_delete_safety_wit_10 : reverse_delete_safety_wit_10.
Axiom proof_of_reverse_delete_safety_wit_11 : reverse_delete_safety_wit_11.
Axiom proof_of_reverse_delete_safety_wit_12 : reverse_delete_safety_wit_12.
Axiom proof_of_reverse_delete_safety_wit_13 : reverse_delete_safety_wit_13.
Axiom proof_of_reverse_delete_safety_wit_14 : reverse_delete_safety_wit_14.
Axiom proof_of_reverse_delete_safety_wit_15 : reverse_delete_safety_wit_15.
Axiom proof_of_reverse_delete_safety_wit_16 : reverse_delete_safety_wit_16.
Axiom proof_of_reverse_delete_safety_wit_17 : reverse_delete_safety_wit_17.
Axiom proof_of_reverse_delete_safety_wit_18 : reverse_delete_safety_wit_18.
Axiom proof_of_reverse_delete_safety_wit_19 : reverse_delete_safety_wit_19.
Axiom proof_of_reverse_delete_safety_wit_20 : reverse_delete_safety_wit_20.
Axiom proof_of_reverse_delete_safety_wit_21 : reverse_delete_safety_wit_21.
Axiom proof_of_reverse_delete_safety_wit_22 : reverse_delete_safety_wit_22.
Axiom proof_of_reverse_delete_safety_wit_23 : reverse_delete_safety_wit_23.
Axiom proof_of_reverse_delete_safety_wit_24 : reverse_delete_safety_wit_24.
Axiom proof_of_reverse_delete_safety_wit_25 : reverse_delete_safety_wit_25.
Axiom proof_of_reverse_delete_safety_wit_26 : reverse_delete_safety_wit_26.
Axiom proof_of_reverse_delete_safety_wit_27 : reverse_delete_safety_wit_27.
Axiom proof_of_reverse_delete_safety_wit_28 : reverse_delete_safety_wit_28.
Axiom proof_of_reverse_delete_safety_wit_29 : reverse_delete_safety_wit_29.
Axiom proof_of_reverse_delete_safety_wit_30 : reverse_delete_safety_wit_30.
Axiom proof_of_reverse_delete_safety_wit_31 : reverse_delete_safety_wit_31.
Axiom proof_of_reverse_delete_safety_wit_32 : reverse_delete_safety_wit_32.
Axiom proof_of_reverse_delete_safety_wit_33 : reverse_delete_safety_wit_33.
Axiom proof_of_reverse_delete_safety_wit_34 : reverse_delete_safety_wit_34.
Axiom proof_of_reverse_delete_safety_wit_35 : reverse_delete_safety_wit_35.
Axiom proof_of_reverse_delete_safety_wit_36 : reverse_delete_safety_wit_36.
Axiom proof_of_reverse_delete_safety_wit_37 : reverse_delete_safety_wit_37.
Axiom proof_of_reverse_delete_safety_wit_38 : reverse_delete_safety_wit_38.
Axiom proof_of_reverse_delete_safety_wit_39 : reverse_delete_safety_wit_39.
Axiom proof_of_reverse_delete_safety_wit_40 : reverse_delete_safety_wit_40.
Axiom proof_of_reverse_delete_safety_wit_41 : reverse_delete_safety_wit_41.
Axiom proof_of_reverse_delete_safety_wit_42 : reverse_delete_safety_wit_42.
Axiom proof_of_reverse_delete_safety_wit_43 : reverse_delete_safety_wit_43.
Axiom proof_of_reverse_delete_safety_wit_44 : reverse_delete_safety_wit_44.
Axiom proof_of_reverse_delete_safety_wit_45 : reverse_delete_safety_wit_45.
Axiom proof_of_reverse_delete_safety_wit_46 : reverse_delete_safety_wit_46.
Axiom proof_of_reverse_delete_safety_wit_47 : reverse_delete_safety_wit_47.
Axiom proof_of_reverse_delete_safety_wit_48 : reverse_delete_safety_wit_48.
Axiom proof_of_reverse_delete_safety_wit_49 : reverse_delete_safety_wit_49.
Axiom proof_of_reverse_delete_safety_wit_50 : reverse_delete_safety_wit_50.
Axiom proof_of_reverse_delete_safety_wit_51 : reverse_delete_safety_wit_51.
Axiom proof_of_reverse_delete_safety_wit_52 : reverse_delete_safety_wit_52.
Axiom proof_of_reverse_delete_safety_wit_53 : reverse_delete_safety_wit_53.
Axiom proof_of_reverse_delete_safety_wit_54 : reverse_delete_safety_wit_54.
Axiom proof_of_reverse_delete_safety_wit_55 : reverse_delete_safety_wit_55.
Axiom proof_of_reverse_delete_safety_wit_56 : reverse_delete_safety_wit_56.
Axiom proof_of_reverse_delete_safety_wit_57 : reverse_delete_safety_wit_57.
Axiom proof_of_reverse_delete_safety_wit_58 : reverse_delete_safety_wit_58.
Axiom proof_of_reverse_delete_entail_wit_1 : reverse_delete_entail_wit_1.
Axiom proof_of_reverse_delete_entail_wit_2 : reverse_delete_entail_wit_2.
Axiom proof_of_reverse_delete_entail_wit_3_1 : reverse_delete_entail_wit_3_1.
Axiom proof_of_reverse_delete_entail_wit_3_2 : reverse_delete_entail_wit_3_2.
Axiom proof_of_reverse_delete_entail_wit_4 : reverse_delete_entail_wit_4.
Axiom proof_of_reverse_delete_entail_wit_5 : reverse_delete_entail_wit_5.
Axiom proof_of_reverse_delete_entail_wit_6 : reverse_delete_entail_wit_6.
Axiom proof_of_reverse_delete_entail_wit_7_1 : reverse_delete_entail_wit_7_1.
Axiom proof_of_reverse_delete_entail_wit_7_2 : reverse_delete_entail_wit_7_2.
Axiom proof_of_reverse_delete_entail_wit_8_1 : reverse_delete_entail_wit_8_1.
Axiom proof_of_reverse_delete_entail_wit_8_2 : reverse_delete_entail_wit_8_2.
Axiom proof_of_reverse_delete_entail_wit_9_1 : reverse_delete_entail_wit_9_1.
Axiom proof_of_reverse_delete_entail_wit_9_2 : reverse_delete_entail_wit_9_2.
Axiom proof_of_reverse_delete_entail_wit_9_3 : reverse_delete_entail_wit_9_3.
Axiom proof_of_reverse_delete_entail_wit_10_1 : reverse_delete_entail_wit_10_1.
Axiom proof_of_reverse_delete_entail_wit_10_2 : reverse_delete_entail_wit_10_2.
Axiom proof_of_reverse_delete_entail_wit_11_1 : reverse_delete_entail_wit_11_1.
Axiom proof_of_reverse_delete_entail_wit_11_2 : reverse_delete_entail_wit_11_2.
Axiom proof_of_reverse_delete_return_wit_1 : reverse_delete_return_wit_1.
Axiom proof_of_reverse_delete_return_wit_2 : reverse_delete_return_wit_2.
Axiom proof_of_reverse_delete_partial_solve_wit_1 : reverse_delete_partial_solve_wit_1.
Axiom proof_of_reverse_delete_partial_solve_wit_2_pure : reverse_delete_partial_solve_wit_2_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_2 : reverse_delete_partial_solve_wit_2.
Axiom proof_of_reverse_delete_partial_solve_wit_3_pure : reverse_delete_partial_solve_wit_3_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_3 : reverse_delete_partial_solve_wit_3.
Axiom proof_of_reverse_delete_partial_solve_wit_4_pure : reverse_delete_partial_solve_wit_4_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_4 : reverse_delete_partial_solve_wit_4.
Axiom proof_of_reverse_delete_partial_solve_wit_5_pure : reverse_delete_partial_solve_wit_5_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_5 : reverse_delete_partial_solve_wit_5.
Axiom proof_of_reverse_delete_partial_solve_wit_6 : reverse_delete_partial_solve_wit_6.
Axiom proof_of_reverse_delete_partial_solve_wit_7 : reverse_delete_partial_solve_wit_7.
Axiom proof_of_reverse_delete_partial_solve_wit_8_pure : reverse_delete_partial_solve_wit_8_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_8 : reverse_delete_partial_solve_wit_8.
Axiom proof_of_reverse_delete_partial_solve_wit_9 : reverse_delete_partial_solve_wit_9.
Axiom proof_of_reverse_delete_partial_solve_wit_10 : reverse_delete_partial_solve_wit_10.
Axiom proof_of_reverse_delete_partial_solve_wit_11 : reverse_delete_partial_solve_wit_11.
Axiom proof_of_reverse_delete_partial_solve_wit_12 : reverse_delete_partial_solve_wit_12.
Axiom proof_of_reverse_delete_partial_solve_wit_13 : reverse_delete_partial_solve_wit_13.
Axiom proof_of_reverse_delete_partial_solve_wit_14_pure : reverse_delete_partial_solve_wit_14_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_14 : reverse_delete_partial_solve_wit_14.
Axiom proof_of_reverse_delete_partial_solve_wit_15 : reverse_delete_partial_solve_wit_15.
Axiom proof_of_reverse_delete_partial_solve_wit_16 : reverse_delete_partial_solve_wit_16.
Axiom proof_of_reverse_delete_partial_solve_wit_17 : reverse_delete_partial_solve_wit_17.
Axiom proof_of_reverse_delete_partial_solve_wit_18 : reverse_delete_partial_solve_wit_18.
Axiom proof_of_reverse_delete_partial_solve_wit_19 : reverse_delete_partial_solve_wit_19.
Axiom proof_of_reverse_delete_partial_solve_wit_20 : reverse_delete_partial_solve_wit_20.
Axiom proof_of_reverse_delete_partial_solve_wit_21 : reverse_delete_partial_solve_wit_21.
Axiom proof_of_reverse_delete_partial_solve_wit_22 : reverse_delete_partial_solve_wit_22.
Axiom proof_of_reverse_delete_partial_solve_wit_23 : reverse_delete_partial_solve_wit_23.
Axiom proof_of_reverse_delete_partial_solve_wit_24 : reverse_delete_partial_solve_wit_24.

End VC_Correct.
