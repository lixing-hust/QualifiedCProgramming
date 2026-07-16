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
Require Import coins_64.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function vowels_count -----*)

Definition vowels_count_safety_wit_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_64_pre_z str_l )) (PreH4 : ((string_length (str_l)) < INT_MAX)) ,
  (store_stringLit (LitMap (("aeiouAEIOU"%string))) ("aeiouAEIOU"%string) )
  **  (GlobalStrings_missing LitMap (cons (("aeiouAEIOU"%string)) ((@nil string))) )
  **  ((( &( "vowels" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vowels_count_safety_wit_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (vowels: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "count" ) )) # Int  |->_)
  **  (store_string s_pre str_l )
  **  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vowels_count_safety_wit_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (vowels: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (store_string s_pre str_l )
  **  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vowels_count_safety_wit_4 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (store_string vowels vowel_payload_64 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vowels_count_safety_wit_5 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (store_string vowels vowel_payload_64 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition vowels_count_safety_wit_6 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (store_string vowels vowel_payload_64 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vowels_count_safety_wit_7 := 
forall (s_pre: Z) (str_l: (@list Z)) (n: Z) (vowels: Z) (i: Z) (count: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_regular_step_64 str_l i count )) (PreH15 : (vowel_count_state_64 str_l (i + 1 ) count )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition vowels_count_safety_wit_8 := 
forall (s_pre: Z) (str_l: (@list Z)) (n: Z) (vowels: Z) (i: Z) (count: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= i)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_miss_step_64 str_l i count )) (PreH15 : (vowel_count_state_64 str_l (i + 1 ) count )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition vowels_count_safety_wit_9 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= i)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_64_pre_z str_l )) (PreH11 : (vowel_payload_safe_64 )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition vowels_count_safety_wit_10 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= i)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition vowels_count_safety_wit_11 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= i)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vowels_count_safety_wit_12 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= i)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth (n - 1 ) (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (121 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 121) ”
.

Definition vowels_count_safety_wit_13 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH2 : (n > 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= count)) (PreH9 : (count <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth (n - 1 ) (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (89 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 89) ”
.

Definition vowels_count_safety_wit_14 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH2 : (n > 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= count)) (PreH9 : (count <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth (n - 1 ) (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition vowels_count_safety_wit_15 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH2 : (n > 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= count)) (PreH9 : (count <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth (n - 1 ) (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vowels_count_safety_wit_16 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH2 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH3 : (n > 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth (n - 1 ) (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition vowels_count_safety_wit_17 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH2 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH3 : (n > 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth (n - 1 ) (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition vowels_count_entail_wit_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_64_pre_z str_l )) (PreH4 : ((string_length (str_l)) < INT_MAX)) ,
  (store_stringLit (LitMap (("aeiouAEIOU"%string))) ("aeiouAEIOU"%string) )
  **  (GlobalStrings_missing LitMap (cons (("aeiouAEIOU"%string)) ((@nil string))) )
  **  (store_string s_pre str_l )
|--
  “ (((LitMap (("aeiouAEIOU"%string))) + (0 * sizeof(CHAR) ) ) = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  (store_string s_pre str_l )
  **  (store_string ((LitMap (("aeiouAEIOU"%string))) + (0 * sizeof(CHAR) ) ) vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_64_pre_z str_l )) (PreH5 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings LitMap )
|--
  “ (vowel_payload_safe_64 ) ” 
  &&  “ (((LitMap (("aeiouAEIOU"%string))) + (0 * sizeof(CHAR) ) ) = (vowel_ptr_64 (LitMap))) ”
  &&  (CharArray.full ((LitMap (("aeiouAEIOU"%string))) + (0 * sizeof(CHAR) ) ) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_1_split_goal_1 := 
forall (str_l: (@list Z)) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_64_pre_z str_l )) (PreH5 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings LitMap )
|--
  “ (vowel_payload_safe_64 ) ”
.

Definition vowels_count_entail_wit_1_split_goal_2 := 
forall (str_l: (@list Z)) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_64_pre_z str_l )) (PreH5 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("aeiouAEIOU"%string))) + (0 * sizeof(CHAR) ) ) = (vowel_ptr_64 (LitMap))) ”
.

Definition vowels_count_entail_wit_1_split_goal_spatial := 
forall (str_l: (@list Z)) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_64_pre_z str_l )) (PreH5 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings LitMap )
|--
  (CharArray.full ((LitMap (("aeiouAEIOU"%string))) + (0 * sizeof(CHAR) ) ) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (vowels: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string s_pre str_l )
  **  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (retval = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l 0 0 ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (vowels: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l 0 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_2_split_goal_1 := 
forall (str_l: (@list Z)) (vowels: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l 0 0 ) ”
.

Definition vowels_count_entail_wit_2_split_goal_2 := 
forall (str_l: (@list Z)) (vowels: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= retval) ”
.

Definition vowels_count_entail_wit_2_split_goal_spatial := 
forall (str_l: (@list Z)) (vowels: Z) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_3 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (store_string vowels vowel_payload_64 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_regular_step_64 str_l i (count + 1 ) ) ” 
  &&  “ (vowel_count_state_64 str_l (i + 1 ) (count + 1 ) ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l (i + 1 ) (count + 1 ) ) ” 
  &&  “ (vowel_regular_step_64 str_l i (count + 1 ) ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_3_split_goal_1 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l (i + 1 ) (count + 1 ) ) ”
.

Definition vowels_count_entail_wit_3_split_goal_2 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_regular_step_64 str_l i (count + 1 ) ) ”
.

Definition vowels_count_entail_wit_3_split_goal_3 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition vowels_count_entail_wit_3_split_goal_4 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition vowels_count_entail_wit_3_split_goal_spatial := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_4 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (store_string vowels vowel_payload_64 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_miss_step_64 str_l i count ) ” 
  &&  “ (vowel_count_state_64 str_l (i + 1 ) count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l (i + 1 ) count ) ” 
  &&  “ (vowel_miss_step_64 str_l i count ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_4_split_goal_1 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l (i + 1 ) count ) ”
.

Definition vowels_count_entail_wit_4_split_goal_2 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_miss_step_64 str_l i count ) ”
.

Definition vowels_count_entail_wit_4_split_goal_3 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition vowels_count_entail_wit_4_split_goal_4 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition vowels_count_entail_wit_4_split_goal_spatial := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_64 (Znth i (c_string (str_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_5_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (n: Z) (vowels: Z) (i: Z) (count: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_regular_step_64 str_l i count )) (PreH15 : (vowel_count_state_64 str_l (i + 1 ) count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l (i + 1 ) count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_5_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (n: Z) (vowels: Z) (i: Z) (count: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= i)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_miss_step_64 str_l i count )) (PreH15 : (vowel_count_state_64 str_l (i + 1 ) count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l (i + 1 ) count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_6_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH2 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH3 : (n > 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= (Znth (n - 1 ) (c_string (str_l)) 0)) ” 
  &&  “ ((Znth (n - 1 ) (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l n ((count + 1 ) - 1 ) ) ” 
  &&  “ (vowel_final_y_64 str_l (count + 1 ) ) ” 
  &&  “ (problem_64_spec_z str_l (count + 1 ) ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l (count + 1 ) ) ” 
  &&  “ (vowel_final_y_64 str_l (count + 1 ) ) ” 
  &&  “ (vowel_count_state_64 str_l n ((count + 1 ) - 1 ) ) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_6_1_split_goal_1 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l (count + 1 ) ) ”
.

Definition vowels_count_entail_wit_6_1_split_goal_2 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_final_y_64 str_l (count + 1 ) ) ”
.

Definition vowels_count_entail_wit_6_1_split_goal_3 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l n ((count + 1 ) - 1 ) ) ”
.

Definition vowels_count_entail_wit_6_1_split_goal_spatial := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_6_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH2 : (n > 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= count)) (PreH9 : (count <= i)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l i count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= (Znth (n - 1 ) (c_string (str_l)) 0)) ” 
  &&  “ ((Znth (n - 1 ) (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l n ((count + 1 ) - 1 ) ) ” 
  &&  “ (vowel_final_y_64 str_l (count + 1 ) ) ” 
  &&  “ (problem_64_spec_z str_l (count + 1 ) ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH4 : (n > 0)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l (count + 1 ) ) ” 
  &&  “ (vowel_final_y_64 str_l (count + 1 ) ) ” 
  &&  “ (vowel_count_state_64 str_l n ((count + 1 ) - 1 ) ) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_6_2_split_goal_1 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH4 : (n > 0)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l (count + 1 ) ) ”
.

Definition vowels_count_entail_wit_6_2_split_goal_2 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH4 : (n > 0)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_final_y_64 str_l (count + 1 ) ) ”
.

Definition vowels_count_entail_wit_6_2_split_goal_3 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH4 : (n > 0)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l n ((count + 1 ) - 1 ) ) ”
.

Definition vowels_count_entail_wit_6_2_split_goal_spatial := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) = 121)) (PreH4 : (n > 0)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= count)) (PreH11 : (count <= i)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_64_pre_z str_l )) (PreH15 : (vowel_payload_safe_64 )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_7 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH2 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH3 : (n > 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n) ” 
  &&  “ (0 <= (Znth (n - 1 ) (c_string (str_l)) 0)) ” 
  &&  “ ((Znth (n - 1 ) (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l n count ) ” 
  &&  “ (vowel_final_not_y_64 str_l count ) ” 
  &&  “ (problem_64_spec_z str_l count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l count ) ” 
  &&  “ (vowel_final_not_y_64 str_l count ) ” 
  &&  “ (vowel_count_state_64 str_l n count ) ” 
  &&  “ ((Znth (n - 1 ) (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth (n - 1 ) (c_string (str_l)) 0)) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_7_split_goal_1 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l count ) ”
.

Definition vowels_count_entail_wit_7_split_goal_2 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_final_not_y_64 str_l count ) ”
.

Definition vowels_count_entail_wit_7_split_goal_3 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l n count ) ”
.

Definition vowels_count_entail_wit_7_split_goal_4 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((Znth (n - 1 ) (c_string (str_l)) 0) <= 127) ”
.

Definition vowels_count_entail_wit_7_split_goal_5 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= (Znth (n - 1 ) (c_string (str_l)) 0)) ”
.

Definition vowels_count_entail_wit_7_split_goal_spatial := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 89)) (PreH4 : ((Znth (n - 1 ) (c_string (str_l)) 0) <> 121)) (PreH5 : (n > 0)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= count)) (PreH12 : (count <= i)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_64_pre_z str_l )) (PreH16 : (vowel_payload_safe_64 )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_entail_wit_8 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= i)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_64_pre_z str_l )) (PreH12 : (vowel_payload_safe_64 )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (vowel_count_state_64 str_l i count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (n = 0) ” 
  &&  “ (count = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l n count ) ” 
  &&  “ (vowel_final_empty_64 str_l count ) ” 
  &&  “ (problem_64_spec_z str_l count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n <= 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l count ) ” 
  &&  “ (vowel_final_empty_64 str_l count ) ” 
  &&  “ (vowel_count_state_64 str_l n count ) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_entail_wit_8_split_goal_1 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n <= 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l count ) ”
.

Definition vowels_count_entail_wit_8_split_goal_2 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n <= 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_final_empty_64 str_l count ) ”
.

Definition vowels_count_entail_wit_8_split_goal_3 := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n <= 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (vowel_count_state_64 str_l n count ) ”
.

Definition vowels_count_entail_wit_8_split_goal_spatial := 
forall (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n <= 0)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= i)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_64_pre_z str_l )) (PreH14 : (vowel_payload_safe_64 )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (vowel_count_state_64 str_l i count )) ,
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_return_wit_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH3 : (n > 0)) (PreH4 : (0 <= count)) (PreH5 : (count <= (n + 1 ))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_64_pre_z str_l )) (PreH11 : (vowel_payload_safe_64 )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (vowel_count_state_64 str_l n (count - 1 ) )) (PreH14 : (vowel_final_y_64 str_l count )) (PreH15 : (problem_64_spec_z str_l count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string (vowel_ptr_64 (LitMap)) vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (ch: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (n > 0)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n + 1 ))) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l n (count - 1 ) )) (PreH16 : (vowel_final_y_64 str_l count )) (PreH17 : (problem_64_spec_z str_l count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (CharArray.full (vowel_ptr_64 (LitMap)) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_return_wit_1_split_goal_spatial := 
forall (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (ch: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (n > 0)) (PreH6 : (0 <= count)) (PreH7 : (count <= (n + 1 ))) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l n (count - 1 ) )) (PreH16 : (vowel_final_y_64 str_l count )) (PreH17 : (problem_64_spec_z str_l count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (CharArray.full (vowel_ptr_64 (LitMap)) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_return_wit_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH3 : (n > 0)) (PreH4 : (0 <= count)) (PreH5 : (count <= n)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_64_pre_z str_l )) (PreH11 : (vowel_payload_safe_64 )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (vowel_count_state_64 str_l n count )) (PreH14 : (vowel_final_not_y_64 str_l count )) (PreH15 : (problem_64_spec_z str_l count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string (vowel_ptr_64 (LitMap)) vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (ch: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (n > 0)) (PreH6 : (0 <= count)) (PreH7 : (count <= n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l n count )) (PreH16 : (vowel_final_not_y_64 str_l count )) (PreH17 : (problem_64_spec_z str_l count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (CharArray.full (vowel_ptr_64 (LitMap)) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_return_wit_2_split_goal_spatial := 
forall (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (ch: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (n > 0)) (PreH6 : (0 <= count)) (PreH7 : (count <= n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_64_pre_z str_l )) (PreH13 : (vowel_payload_safe_64 )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (vowel_count_state_64 str_l n count )) (PreH16 : (vowel_final_not_y_64 str_l count )) (PreH17 : (problem_64_spec_z str_l count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (CharArray.full (vowel_ptr_64 (LitMap)) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_return_wit_3 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH3 : (n = 0)) (PreH4 : (count = 0)) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_64_pre_z str_l )) (PreH8 : (vowel_payload_safe_64 )) (PreH9 : ((string_length (str_l)) < INT_MAX)) (PreH10 : (vowel_count_state_64 str_l n count )) (PreH11 : (vowel_final_empty_64 str_l count )) (PreH12 : (problem_64_spec_z str_l count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (problem_64_spec_z str_l count ) ”
  &&  (store_string s_pre str_l )
  **  (store_string (vowel_ptr_64 (LitMap)) vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
) \/
(
forall (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (n = 0)) (PreH6 : (count = 0)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_64_pre_z str_l )) (PreH10 : (vowel_payload_safe_64 )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (vowel_count_state_64 str_l n count )) (PreH13 : (vowel_final_empty_64 str_l count )) (PreH14 : (problem_64_spec_z str_l count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (CharArray.full (vowel_ptr_64 (LitMap)) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
).

Definition vowels_count_return_wit_3_split_goal_spatial := 
forall (str_l: (@list Z)) (n: Z) (vowels: Z) (count: Z) (PreH1 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH5 : (n = 0)) (PreH6 : (count = 0)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_64_pre_z str_l )) (PreH10 : (vowel_payload_safe_64 )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (vowel_count_state_64 str_l n count )) (PreH13 : (vowel_final_empty_64 str_l count )) (PreH14 : (problem_64_spec_z str_l count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  (CharArray.full (vowel_ptr_64 (LitMap)) ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_partial_solve_wit_1_pure := 
forall (s_pre: Z) (str_l: (@list Z)) (vowels: Z) (PreH1 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_64_pre_z str_l )) (PreH5 : (vowel_payload_safe_64 )) (PreH6 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition vowels_count_partial_solve_wit_1_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (vowels: Z) (PreH1 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH2 : (valid_string str_l )) (PreH3 : (all_ascii str_l )) (PreH4 : (problem_64_pre_z str_l )) (PreH5 : (vowel_payload_safe_64 )) (PreH6 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (vowel_payload_64)) + 1 )) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_partial_solve_wit_1 := vowels_count_partial_solve_wit_1_pure -> vowels_count_partial_solve_wit_1_aux.

Definition vowels_count_partial_solve_wit_2_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= i)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_64_pre_z str_l )) (PreH11 : (vowel_payload_safe_64 )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (vowel_count_state_64 str_l i count )) ,
  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((string_length (vowel_payload_64)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ (valid_string vowel_payload_64 ) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (count <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (count >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= count)) (PreH17 : (count <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_64_pre_z str_l )) (PreH21 : (vowel_payload_safe_64 )) (PreH22 : ((string_length (str_l)) < INT_MAX)) (PreH23 : (vowel_count_state_64 str_l i count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (valid_string vowel_payload_64 ) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ((string_length (vowel_payload_64)) < INT_MAX) ”
).

Definition vowels_count_partial_solve_wit_2_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (count <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (count >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= count)) (PreH17 : (count <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_64_pre_z str_l )) (PreH21 : (vowel_payload_safe_64 )) (PreH22 : ((string_length (str_l)) < INT_MAX)) (PreH23 : (vowel_count_state_64 str_l i count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (valid_string vowel_payload_64 ) ”
.

Definition vowels_count_partial_solve_wit_2_pure_split_goal_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (count <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (count >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= count)) (PreH17 : (count <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_64_pre_z str_l )) (PreH21 : (vowel_payload_safe_64 )) (PreH22 : ((string_length (str_l)) < INT_MAX)) (PreH23 : (vowel_count_state_64 str_l i count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition vowels_count_partial_solve_wit_2_pure_split_goal_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (count <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (count >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= count)) (PreH17 : (count <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_64_pre_z str_l )) (PreH21 : (vowel_payload_safe_64 )) (PreH22 : ((string_length (str_l)) < INT_MAX)) (PreH23 : (vowel_count_state_64 str_l i count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition vowels_count_partial_solve_wit_2_pure_split_goal_4 := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (count <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (count >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_64)) + 1 ))) (PreH10 : (0 <= ((string_length (str_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (0 <= count)) (PreH17 : (count <= i)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_64_pre_z str_l )) (PreH21 : (vowel_payload_safe_64 )) (PreH22 : ((string_length (str_l)) < INT_MAX)) (PreH23 : (vowel_count_state_64 str_l i count )) ,
  (CharArray.full vowels ((string_length (vowel_payload_64)) + 1 ) (c_string (vowel_payload_64)) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((string_length (vowel_payload_64)) < INT_MAX) ”
.

Definition vowels_count_partial_solve_wit_2_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (count: Z) (i: Z) (vowels: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (vowels = (vowel_ptr_64 (LitMap)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= i)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_64_pre_z str_l )) (PreH11 : (vowel_payload_safe_64 )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (vowel_count_state_64 str_l i count )) ,
  (store_string s_pre str_l )
  **  (store_string vowels vowel_payload_64 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
|--
  “ ((string_length (vowel_payload_64)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ (valid_string vowel_payload_64 ) ” 
  &&  “ (0 <= ((string_length (vowel_payload_64)) + 1 )) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (vowels = (vowel_ptr_64 (LitMap))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_64_pre_z str_l ) ” 
  &&  “ (vowel_payload_safe_64 ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (vowel_count_state_64 str_l i count ) ”
  &&  (store_string vowels vowel_payload_64 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_64 )
.

Definition vowels_count_partial_solve_wit_2 := vowels_count_partial_solve_wit_2_pure -> vowels_count_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_vowels_count_safety_wit_1 : vowels_count_safety_wit_1.
Axiom proof_of_vowels_count_safety_wit_2 : vowels_count_safety_wit_2.
Axiom proof_of_vowels_count_safety_wit_3 : vowels_count_safety_wit_3.
Axiom proof_of_vowels_count_safety_wit_4 : vowels_count_safety_wit_4.
Axiom proof_of_vowels_count_safety_wit_5 : vowels_count_safety_wit_5.
Axiom proof_of_vowels_count_safety_wit_6 : vowels_count_safety_wit_6.
Axiom proof_of_vowels_count_safety_wit_7 : vowels_count_safety_wit_7.
Axiom proof_of_vowels_count_safety_wit_8 : vowels_count_safety_wit_8.
Axiom proof_of_vowels_count_safety_wit_9 : vowels_count_safety_wit_9.
Axiom proof_of_vowels_count_safety_wit_10 : vowels_count_safety_wit_10.
Axiom proof_of_vowels_count_safety_wit_11 : vowels_count_safety_wit_11.
Axiom proof_of_vowels_count_safety_wit_12 : vowels_count_safety_wit_12.
Axiom proof_of_vowels_count_safety_wit_13 : vowels_count_safety_wit_13.
Axiom proof_of_vowels_count_safety_wit_14 : vowels_count_safety_wit_14.
Axiom proof_of_vowels_count_safety_wit_15 : vowels_count_safety_wit_15.
Axiom proof_of_vowels_count_safety_wit_16 : vowels_count_safety_wit_16.
Axiom proof_of_vowels_count_safety_wit_17 : vowels_count_safety_wit_17.
Axiom proof_of_vowels_count_entail_wit_1 : vowels_count_entail_wit_1.
Axiom proof_of_vowels_count_entail_wit_2 : vowels_count_entail_wit_2.
Axiom proof_of_vowels_count_entail_wit_3 : vowels_count_entail_wit_3.
Axiom proof_of_vowels_count_entail_wit_4 : vowels_count_entail_wit_4.
Axiom proof_of_vowels_count_entail_wit_5_1 : vowels_count_entail_wit_5_1.
Axiom proof_of_vowels_count_entail_wit_5_2 : vowels_count_entail_wit_5_2.
Axiom proof_of_vowels_count_entail_wit_6_1 : vowels_count_entail_wit_6_1.
Axiom proof_of_vowels_count_entail_wit_6_2 : vowels_count_entail_wit_6_2.
Axiom proof_of_vowels_count_entail_wit_7 : vowels_count_entail_wit_7.
Axiom proof_of_vowels_count_entail_wit_8 : vowels_count_entail_wit_8.
Axiom proof_of_vowels_count_return_wit_1 : vowels_count_return_wit_1.
Axiom proof_of_vowels_count_return_wit_2 : vowels_count_return_wit_2.
Axiom proof_of_vowels_count_return_wit_3 : vowels_count_return_wit_3.
Axiom proof_of_vowels_count_partial_solve_wit_1_pure : vowels_count_partial_solve_wit_1_pure.
Axiom proof_of_vowels_count_partial_solve_wit_1 : vowels_count_partial_solve_wit_1.
Axiom proof_of_vowels_count_partial_solve_wit_2_pure : vowels_count_partial_solve_wit_2_pure.
Axiom proof_of_vowels_count_partial_solve_wit_2 : vowels_count_partial_solve_wit_2.

End VC_Correct.
