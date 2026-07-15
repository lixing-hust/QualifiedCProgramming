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
Require Import coins_78.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function hex_key -----*)

Definition hex_key_safety_wit_1 := 
forall (num_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_78_pre_z str_l )) (PreH4 : (hex_count_safe_78 str_l )) (PreH5 : (key_payload_safe_78 )) (PreH6 : ((string_length (str_l)) < INT_MAX)) ,
  (store_stringLit (LitMap (("2357BD"%string))) ("2357BD"%string) )
  **  (GlobalStrings_missing LitMap (cons (("2357BD"%string)) ((@nil string))) )
  **  ((( &( "key" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  (store_string num_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hex_key_safety_wit_2 := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "out" ) )) # Int  |->_)
  **  (store_string num_pre str_l )
  **  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hex_key_safety_wit_3 := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  (store_string num_pre str_l )
  **  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hex_key_safety_wit_4 := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (i < n)) (PreH5 : (key = (key_ptr_78 (LitMap)))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out)) (PreH10 : (out <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_78_pre_z str_l )) (PreH14 : (hex_count_safe_78 str_l )) (PreH15 : (key_payload_safe_78 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (hex_count_state_78 str_l i out )) ,
  (store_string key key_payload_78 )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hex_key_safety_wit_5 := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (store_string key key_payload_78 )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((out + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out + 1 )) ”
.

Definition hex_key_safety_wit_6 := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (store_string key key_payload_78 )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hex_key_safety_wit_7 := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (n: Z) (i: Z) (out: Z) (ch: Z) (PreH1 : (key = (key_ptr_78 (LitMap)))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= out)) (PreH6 : (out <= (i + 1 ))) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_78_pre_z str_l )) (PreH12 : (hex_count_safe_78 str_l )) (PreH13 : (key_payload_safe_78 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (hex_hit_step_78 str_l i out )) (PreH16 : (hex_count_state_78 str_l (i + 1 ) out )) ,
  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition hex_key_safety_wit_8 := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (n: Z) (i: Z) (out: Z) (ch: Z) (PreH1 : (key = (key_ptr_78 (LitMap)))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= out)) (PreH6 : (out <= i)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_78_pre_z str_l )) (PreH12 : (hex_count_safe_78 str_l )) (PreH13 : (key_payload_safe_78 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (hex_miss_step_78 str_l i out )) (PreH16 : (hex_count_state_78 str_l (i + 1 ) out )) ,
  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition hex_key_entail_wit_1 := 
(
forall (num_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_78_pre_z str_l )) (PreH4 : (hex_count_safe_78 str_l )) (PreH5 : (key_payload_safe_78 )) (PreH6 : ((string_length (str_l)) < INT_MAX)) ,
  (store_stringLit (LitMap (("2357BD"%string))) ("2357BD"%string) )
  **  (GlobalStrings_missing LitMap (cons (("2357BD"%string)) ((@nil string))) )
  **  (store_string num_pre str_l )
|--
  “ (((LitMap (("2357BD"%string))) + (0 * sizeof(CHAR) ) ) = (key_ptr_78 (LitMap))) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  (store_string num_pre str_l )
  **  (store_string ((LitMap (("2357BD"%string))) + (0 * sizeof(CHAR) ) ) key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
) \/
(
forall (str_l: (@list Z)) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_78_pre_z str_l )) (PreH5 : (hex_count_safe_78 str_l )) (PreH6 : (key_payload_safe_78 )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("2357BD"%string))) + (0 * sizeof(CHAR) ) ) = (key_ptr_78 (LitMap))) ”
  &&  (CharArray.full ((LitMap (("2357BD"%string))) + (0 * sizeof(CHAR) ) ) ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
).

Definition hex_key_entail_wit_1_split_goal_1 := 
forall (str_l: (@list Z)) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_78_pre_z str_l )) (PreH5 : (hex_count_safe_78 str_l )) (PreH6 : (key_payload_safe_78 )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("2357BD"%string))) + (0 * sizeof(CHAR) ) ) = (key_ptr_78 (LitMap))) ”
.

Definition hex_key_entail_wit_1_split_goal_spatial := 
forall (str_l: (@list Z)) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_78_pre_z str_l )) (PreH5 : (hex_count_safe_78 str_l )) (PreH6 : (key_payload_safe_78 )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings LitMap )
|--
  (CharArray.full ((LitMap (("2357BD"%string))) + (0 * sizeof(CHAR) ) ) ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_entail_wit_2 := 
(
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string num_pre str_l )
  **  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (hex_count_state_78 str_l 0 0 ) ”
  &&  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
) \/
(
forall (str_l: (@list Z)) (key: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_count_state_78 str_l 0 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  (GlobalStrings_missing LitMap all_key_literals_78 )
).

Definition hex_key_entail_wit_2_split_goal_1 := 
forall (str_l: (@list Z)) (key: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_count_state_78 str_l 0 0 ) ”
.

Definition hex_key_entail_wit_2_split_goal_2 := 
forall (str_l: (@list Z)) (key: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (0 <= retval) ”
.

Definition hex_key_entail_wit_2_split_goal_spatial := 
forall (str_l: (@list Z)) (key: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_entail_wit_3 := 
(
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (store_string key key_payload_78 )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (out + 1 )) ” 
  &&  “ ((out + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (hex_hit_step_78 str_l i (out + 1 ) ) ” 
  &&  “ (hex_count_state_78 str_l (i + 1 ) (out + 1 ) ) ”
  &&  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
) \/
(
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_count_state_78 str_l (i + 1 ) (out + 1 ) ) ” 
  &&  “ (hex_hit_step_78 str_l i (out + 1 ) ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  (GlobalStrings_missing LitMap all_key_literals_78 )
).

Definition hex_key_entail_wit_3_split_goal_1 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_count_state_78 str_l (i + 1 ) (out + 1 ) ) ”
.

Definition hex_key_entail_wit_3_split_goal_2 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_hit_step_78 str_l i (out + 1 ) ) ”
.

Definition hex_key_entail_wit_3_split_goal_3 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition hex_key_entail_wit_3_split_goal_4 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition hex_key_entail_wit_3_split_goal_spatial := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_entail_wit_4 := 
(
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (store_string key key_payload_78 )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (hex_miss_step_78 str_l i out ) ” 
  &&  “ (hex_count_state_78 str_l (i + 1 ) out ) ”
  &&  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
) \/
(
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_count_state_78 str_l (i + 1 ) out ) ” 
  &&  “ (hex_miss_step_78 str_l i out ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  (GlobalStrings_missing LitMap all_key_literals_78 )
).

Definition hex_key_entail_wit_4_split_goal_1 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_count_state_78 str_l (i + 1 ) out ) ”
.

Definition hex_key_entail_wit_4_split_goal_2 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_miss_step_78 str_l i out ) ”
.

Definition hex_key_entail_wit_4_split_goal_3 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition hex_key_entail_wit_4_split_goal_4 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition hex_key_entail_wit_4_split_goal_spatial := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result key_payload_78 (Znth i (c_string (str_l)) 0) retval key )) (PreH3 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (key = (key_ptr_78 (LitMap)))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= out)) (PreH11 : (out <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_78_pre_z str_l )) (PreH15 : (hex_count_safe_78 str_l )) (PreH16 : (key_payload_safe_78 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_entail_wit_5_1 := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (n: Z) (i: Z) (out: Z) (ch: Z) (PreH1 : (key = (key_ptr_78 (LitMap)))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= out)) (PreH6 : (out <= (i + 1 ))) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_78_pre_z str_l )) (PreH12 : (hex_count_safe_78 str_l )) (PreH13 : (key_payload_safe_78 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (hex_hit_step_78 str_l i out )) (PreH16 : (hex_count_state_78 str_l (i + 1 ) out )) ,
  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (hex_count_state_78 str_l (i + 1 ) out ) ”
  &&  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_entail_wit_5_2 := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (n: Z) (i: Z) (out: Z) (ch: Z) (PreH1 : (key = (key_ptr_78 (LitMap)))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= out)) (PreH6 : (out <= i)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_78_pre_z str_l )) (PreH12 : (hex_count_safe_78 str_l )) (PreH13 : (key_payload_safe_78 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (hex_miss_step_78 str_l i out )) (PreH16 : (hex_count_state_78 str_l (i + 1 ) out )) ,
  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (hex_count_state_78 str_l (i + 1 ) out ) ”
  &&  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_entail_wit_6 := 
(
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (i >= n)) (PreH2 : (key = (key_ptr_78 (LitMap)))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= out)) (PreH7 : (out <= i)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_78_pre_z str_l )) (PreH11 : (hex_count_safe_78 str_l )) (PreH12 : (key_payload_safe_78 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (hex_count_state_78 str_l i out )) ,
  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= n) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (hex_count_state_78 str_l n out ) ” 
  &&  “ (hex_final_78 str_l out ) ” 
  &&  “ (problem_78_spec_z str_l out ) ”
  &&  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
) \/
(
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= out)) (PreH9 : (out <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_78_pre_z str_l )) (PreH13 : (hex_count_safe_78 str_l )) (PreH14 : (key_payload_safe_78 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (problem_78_spec_z str_l out ) ” 
  &&  “ (hex_final_78 str_l out ) ” 
  &&  “ (hex_count_state_78 str_l n out ) ”
  &&  (GlobalStrings_missing LitMap all_key_literals_78 )
).

Definition hex_key_entail_wit_6_split_goal_1 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= out)) (PreH9 : (out <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_78_pre_z str_l )) (PreH13 : (hex_count_safe_78 str_l )) (PreH14 : (key_payload_safe_78 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (problem_78_spec_z str_l out ) ”
.

Definition hex_key_entail_wit_6_split_goal_2 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= out)) (PreH9 : (out <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_78_pre_z str_l )) (PreH13 : (hex_count_safe_78 str_l )) (PreH14 : (key_payload_safe_78 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_final_78 str_l out ) ”
.

Definition hex_key_entail_wit_6_split_goal_3 := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= out)) (PreH9 : (out <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_78_pre_z str_l )) (PreH13 : (hex_count_safe_78 str_l )) (PreH14 : (key_payload_safe_78 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (hex_count_state_78 str_l n out ) ”
.

Definition hex_key_entail_wit_6_split_goal_spatial := 
forall (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (key = (key_ptr_78 (LitMap)))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= out)) (PreH9 : (out <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_78_pre_z str_l )) (PreH13 : (hex_count_safe_78 str_l )) (PreH14 : (key_payload_safe_78 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (hex_count_state_78 str_l i out )) ,
  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_return_wit_1 := 
(
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (n: Z) (out: Z) (PreH1 : (key = (key_ptr_78 (LitMap)))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (0 <= out)) (PreH4 : (out <= n)) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_78_pre_z str_l )) (PreH8 : (hex_count_safe_78 str_l )) (PreH9 : (key_payload_safe_78 )) (PreH10 : ((string_length (str_l)) < INT_MAX)) (PreH11 : (hex_count_state_78 str_l n out )) (PreH12 : (hex_final_78 str_l out )) (PreH13 : (problem_78_spec_z str_l out )) ,
  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (problem_78_spec_z str_l out ) ”
  &&  (store_string num_pre str_l )
  **  (store_string (key_ptr_78 (LitMap)) key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
) \/
(
forall (str_l: (@list Z)) (key: Z) (n: Z) (out: Z) (PreH1 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (key = (key_ptr_78 (LitMap)))) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (0 <= out)) (PreH6 : (out <= n)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_78_pre_z str_l )) (PreH10 : (hex_count_safe_78 str_l )) (PreH11 : (key_payload_safe_78 )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (hex_count_state_78 str_l n out )) (PreH14 : (hex_final_78 str_l out )) (PreH15 : (problem_78_spec_z str_l out )) ,
  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  (CharArray.full (key_ptr_78 (LitMap)) ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
).

Definition hex_key_return_wit_1_split_goal_spatial := 
forall (str_l: (@list Z)) (key: Z) (n: Z) (out: Z) (PreH1 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (key = (key_ptr_78 (LitMap)))) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (0 <= out)) (PreH6 : (out <= n)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_78_pre_z str_l )) (PreH10 : (hex_count_safe_78 str_l )) (PreH11 : (key_payload_safe_78 )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (hex_count_state_78 str_l n out )) (PreH14 : (hex_final_78 str_l out )) (PreH15 : (problem_78_spec_z str_l out )) ,
  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  (CharArray.full (key_ptr_78 (LitMap)) ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_partial_solve_wit_1_pure := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (PreH1 : (key = (key_ptr_78 (LitMap)))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_78_pre_z str_l )) (PreH5 : (hex_count_safe_78 str_l )) (PreH6 : (key_payload_safe_78 )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition hex_key_partial_solve_wit_1_aux := 
forall (num_pre: Z) (str_l: (@list Z)) (key: Z) (PreH1 : (key = (key_ptr_78 (LitMap)))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_78_pre_z str_l )) (PreH5 : (hex_count_safe_78 str_l )) (PreH6 : (key_payload_safe_78 )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (key_payload_78)) + 1 )) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  (store_string num_pre str_l )
  **  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_partial_solve_wit_1 := hex_key_partial_solve_wit_1_pure -> hex_key_partial_solve_wit_1_aux.

Definition hex_key_partial_solve_wit_2_pure := 
(
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (i < n)) (PreH2 : (key = (key_ptr_78 (LitMap)))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= out)) (PreH7 : (out <= i)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_78_pre_z str_l )) (PreH11 : (hex_count_safe_78 str_l )) (PreH12 : (key_payload_safe_78 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (hex_count_state_78 str_l i out )) ,
  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((string_length (key_payload_78)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ (valid_string key_payload_78 ) ”
) \/
(
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (out <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (out >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (key = (key_ptr_78 (LitMap)))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= out)) (PreH17 : (out <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_78_pre_z str_l )) (PreH21 : (hex_count_safe_78 str_l )) (PreH22 : (key_payload_safe_78 )) (PreH23 : ((string_length (str_l)) < INT_MAX)) (PreH24 : (hex_count_state_78 str_l i out )) ,
  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (valid_string key_payload_78 ) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ((string_length (key_payload_78)) < INT_MAX) ”
).

Definition hex_key_partial_solve_wit_2_pure_split_goal_1 := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (out <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (out >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (key = (key_ptr_78 (LitMap)))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= out)) (PreH17 : (out <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_78_pre_z str_l )) (PreH21 : (hex_count_safe_78 str_l )) (PreH22 : (key_payload_safe_78 )) (PreH23 : ((string_length (str_l)) < INT_MAX)) (PreH24 : (hex_count_state_78 str_l i out )) ,
  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (valid_string key_payload_78 ) ”
.

Definition hex_key_partial_solve_wit_2_pure_split_goal_2 := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (out <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (out >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (key = (key_ptr_78 (LitMap)))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= out)) (PreH17 : (out <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_78_pre_z str_l )) (PreH21 : (hex_count_safe_78 str_l )) (PreH22 : (key_payload_safe_78 )) (PreH23 : ((string_length (str_l)) < INT_MAX)) (PreH24 : (hex_count_state_78 str_l i out )) ,
  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition hex_key_partial_solve_wit_2_pure_split_goal_3 := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (out <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (out >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (key = (key_ptr_78 (LitMap)))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= out)) (PreH17 : (out <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_78_pre_z str_l )) (PreH21 : (hex_count_safe_78 str_l )) (PreH22 : (key_payload_safe_78 )) (PreH23 : ((string_length (str_l)) < INT_MAX)) (PreH24 : (hex_count_state_78 str_l i out )) ,
  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition hex_key_partial_solve_wit_2_pure_split_goal_4 := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (out <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (out >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (key_payload_78)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (key = (key_ptr_78 (LitMap)))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= out)) (PreH17 : (out <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_78_pre_z str_l )) (PreH21 : (hex_count_safe_78 str_l )) (PreH22 : (key_payload_safe_78 )) (PreH23 : ((string_length (str_l)) < INT_MAX)) (PreH24 : (hex_count_state_78 str_l i out )) ,
  (CharArray.full key ((string_length (key_payload_78)) + 1 ) (c_string (key_payload_78)) )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((string_length (key_payload_78)) < INT_MAX) ”
.

Definition hex_key_partial_solve_wit_2_aux := 
forall (num_pre: Z) (str_l: (@list Z)) (out: Z) (i: Z) (n: Z) (key: Z) (PreH1 : (i < n)) (PreH2 : (key = (key_ptr_78 (LitMap)))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= out)) (PreH7 : (out <= i)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_78_pre_z str_l )) (PreH11 : (hex_count_safe_78 str_l )) (PreH12 : (key_payload_safe_78 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (hex_count_state_78 str_l i out )) ,
  (store_string num_pre str_l )
  **  (store_string key key_payload_78 )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
|--
  “ ((string_length (key_payload_78)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ (valid_string key_payload_78 ) ” 
  &&  “ (0 <= ((string_length (key_payload_78)) + 1 )) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (key = (key_ptr_78 (LitMap))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= i) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_78_pre_z str_l ) ” 
  &&  “ (hex_count_safe_78 str_l ) ” 
  &&  “ (key_payload_safe_78 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (hex_count_state_78 str_l i out ) ”
  &&  (store_string key key_payload_78 )
  **  (CharArray.full num_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (GlobalStrings_missing LitMap all_key_literals_78 )
.

Definition hex_key_partial_solve_wit_2 := hex_key_partial_solve_wit_2_pure -> hex_key_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_hex_key_safety_wit_1 : hex_key_safety_wit_1.
Axiom proof_of_hex_key_safety_wit_2 : hex_key_safety_wit_2.
Axiom proof_of_hex_key_safety_wit_3 : hex_key_safety_wit_3.
Axiom proof_of_hex_key_safety_wit_4 : hex_key_safety_wit_4.
Axiom proof_of_hex_key_safety_wit_5 : hex_key_safety_wit_5.
Axiom proof_of_hex_key_safety_wit_6 : hex_key_safety_wit_6.
Axiom proof_of_hex_key_safety_wit_7 : hex_key_safety_wit_7.
Axiom proof_of_hex_key_safety_wit_8 : hex_key_safety_wit_8.
Axiom proof_of_hex_key_entail_wit_1 : hex_key_entail_wit_1.
Axiom proof_of_hex_key_entail_wit_2 : hex_key_entail_wit_2.
Axiom proof_of_hex_key_entail_wit_3 : hex_key_entail_wit_3.
Axiom proof_of_hex_key_entail_wit_4 : hex_key_entail_wit_4.
Axiom proof_of_hex_key_entail_wit_5_1 : hex_key_entail_wit_5_1.
Axiom proof_of_hex_key_entail_wit_5_2 : hex_key_entail_wit_5_2.
Axiom proof_of_hex_key_entail_wit_6 : hex_key_entail_wit_6.
Axiom proof_of_hex_key_return_wit_1 : hex_key_return_wit_1.
Axiom proof_of_hex_key_partial_solve_wit_1_pure : hex_key_partial_solve_wit_1_pure.
Axiom proof_of_hex_key_partial_solve_wit_1 : hex_key_partial_solve_wit_1.
Axiom proof_of_hex_key_partial_solve_wit_2_pure : hex_key_partial_solve_wit_2_pure.
Axiom proof_of_hex_key_partial_solve_wit_2 : hex_key_partial_solve_wit_2.

End VC_Correct.
