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
Require Import SimpleC.EE.coins_143.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function words_in_sentence -----*)

Definition words_in_sentence_safety_wit_1 := 
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (sentence_pre = sentence_addr)) (PreH4 : (problem_143_pre_z input )) (PreH5 : (ascii_range_z_143 input )) (PreH6 : (valid_string input )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string sentence_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
) \/
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (sentence_pre = sentence_addr)) (PreH4 : (problem_143_pre_z input )) (PreH5 : (ascii_range_z_143 input )) (PreH6 : (valid_string input )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string sentence_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
).

Definition words_in_sentence_safety_wit_1_split_goal_1 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (sentence_pre = sentence_addr)) (PreH4 : (problem_143_pre_z input )) (PreH5 : (ascii_range_z_143 input )) (PreH6 : (valid_string input )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string sentence_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ”
.

Definition words_in_sentence_safety_wit_1_split_goal_2 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (sentence_pre = sentence_addr)) (PreH4 : (problem_143_pre_z input )) (PreH5 : (ascii_range_z_143 input )) (PreH6 : (valid_string input )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string sentence_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition words_in_sentence_safety_wit_2 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (sentence_pre = sentence_addr)) (PreH4 : (problem_143_pre_z input )) (PreH5 : (ascii_range_z_143 input )) (PreH6 : (valid_string input )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string sentence_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_in_sentence_safety_wit_3 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  ((( &( "out_len" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_4 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_in_sentence_safety_wit_5 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_in_sentence_safety_wit_6 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_7 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  ((( &( "isp" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_8 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "isp" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_9 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "l" ) )) # Int  |-> 0)
  **  ((( &( "isp" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_10 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (0 <= out_len)) (PreH6 : (out_len <= i)) (PreH7 : (out_len <= n)) (PreH8 : (output_gap_outer_143 out_len start i )) (PreH9 : (outer_done_143 i n start )) (PreH10 : (out <> 0)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (INT_MIN <= l)) (PreH14 : (l <= INT_MAX)) (PreH15 : (INT_MIN <= j)) (PreH16 : (j <= INT_MAX)) (PreH17 : ((Zlength (output_l)) = out_len)) (PreH18 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH19 : (PrimeLengthWordsZ143 words selected )) (PreH20 : (output_l = (join_words_z_143 (selected)))) (PreH21 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH22 : (n = (string_length (input)))) (PreH23 : (problem_143_pre_z input )) (PreH24 : (ascii_range_z_143 input )) (PreH25 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition words_in_sentence_safety_wit_11 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_12 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (0 <= out_len)) (PreH6 : (out_len <= i)) (PreH7 : (out_len <= n)) (PreH8 : (output_gap_outer_143 out_len start i )) (PreH9 : (outer_done_143 i n start )) (PreH10 : (out <> 0)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (INT_MIN <= l)) (PreH14 : (l <= INT_MAX)) (PreH15 : (INT_MIN <= j)) (PreH16 : (j <= INT_MAX)) (PreH17 : ((Zlength (output_l)) = out_len)) (PreH18 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH19 : (PrimeLengthWordsZ143 words selected )) (PreH20 : (output_l = (join_words_z_143 (selected)))) (PreH21 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH22 : (n = (string_length (input)))) (PreH23 : (problem_143_pre_z input )) (PreH24 : (ascii_range_z_143 input )) (PreH25 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_13 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_14 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_in_sentence_safety_wit_15 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_in_sentence_safety_wit_16 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition words_in_sentence_safety_wit_17 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition words_in_sentence_safety_wit_18 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition words_in_sentence_safety_wit_19 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition words_in_sentence_safety_wit_20 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) < 2)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_21 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) < 2)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH22 : (PrimeLengthWordsZ143 words selected )) (PreH23 : (output_l = (join_words_z_143 (selected)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_22 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) < 2)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 0)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition words_in_sentence_safety_wit_23 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) < 2)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH22 : (PrimeLengthWordsZ143 words selected )) (PreH23 : (output_l = (join_words_z_143 (selected)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 0)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition words_in_sentence_safety_wit_24 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) >= 2)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition words_in_sentence_safety_wit_25 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) >= 2)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH22 : (PrimeLengthWordsZ143 words selected )) (PreH23 : (output_l = (join_words_z_143 (selected)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "l" ) )) # Int  |-> (i - start ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition words_in_sentence_safety_wit_26 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (l = (i - start ))) (PreH6 : (0 < l)) (PreH7 : (l <= 100)) (PreH8 : (2 <= j)) (PreH9 : (j <= 12)) (PreH10 : (INT_MIN <= isp)) (PreH11 : (isp <= INT_MAX)) (PreH12 : (0 <= out_len)) (PreH13 : (out_len <= i)) (PreH14 : (output_gap_inner_143 out_len start )) (PreH15 : (word_boundary_143 input i n )) (PreH16 : (out <> 0)) (PreH17 : ((Zlength (output_l)) = out_len)) (PreH18 : (SentencePrefix143 input i cur words )) (PreH19 : (PrimeLengthWordsZ143 words selected )) (PreH20 : (output_l = (join_words_z_143 (selected)))) (PreH21 : (current_word_143 input i start cur )) (PreH22 : (prime_scan_state_143 l j isp )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((j * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j * j )) ”
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (l = (i - start ))) (PreH6 : (0 < l)) (PreH7 : (l <= 100)) (PreH8 : (2 <= j)) (PreH9 : (j <= 12)) (PreH10 : (INT_MIN <= isp)) (PreH11 : (isp <= INT_MAX)) (PreH12 : (0 <= out_len)) (PreH13 : (out_len <= i)) (PreH14 : (output_gap_inner_143 out_len start )) (PreH15 : (word_boundary_143 input i n )) (PreH16 : (out <> 0)) (PreH17 : ((Zlength (output_l)) = out_len)) (PreH18 : (SentencePrefix143 input i cur words )) (PreH19 : (PrimeLengthWordsZ143 words selected )) (PreH20 : (output_l = (join_words_z_143 (selected)))) (PreH21 : (current_word_143 input i start cur )) (PreH22 : (prime_scan_state_143 l j isp )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((j * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j * j )) ”
).

Definition words_in_sentence_safety_wit_26_split_goal_1 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (l = (i - start ))) (PreH6 : (0 < l)) (PreH7 : (l <= 100)) (PreH8 : (2 <= j)) (PreH9 : (j <= 12)) (PreH10 : (INT_MIN <= isp)) (PreH11 : (isp <= INT_MAX)) (PreH12 : (0 <= out_len)) (PreH13 : (out_len <= i)) (PreH14 : (output_gap_inner_143 out_len start )) (PreH15 : (word_boundary_143 input i n )) (PreH16 : (out <> 0)) (PreH17 : ((Zlength (output_l)) = out_len)) (PreH18 : (SentencePrefix143 input i cur words )) (PreH19 : (PrimeLengthWordsZ143 words selected )) (PreH20 : (output_l = (join_words_z_143 (selected)))) (PreH21 : (current_word_143 input i start cur )) (PreH22 : (prime_scan_state_143 l j isp )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((j * j ) <= INT_MAX) ”
.

Definition words_in_sentence_safety_wit_26_split_goal_2 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (l = (i - start ))) (PreH6 : (0 < l)) (PreH7 : (l <= 100)) (PreH8 : (2 <= j)) (PreH9 : (j <= 12)) (PreH10 : (INT_MIN <= isp)) (PreH11 : (isp <= INT_MAX)) (PreH12 : (0 <= out_len)) (PreH13 : (out_len <= i)) (PreH14 : (output_gap_inner_143 out_len start )) (PreH15 : (word_boundary_143 input i n )) (PreH16 : (out <> 0)) (PreH17 : ((Zlength (output_l)) = out_len)) (PreH18 : (SentencePrefix143 input i cur words )) (PreH19 : (PrimeLengthWordsZ143 words selected )) (PreH20 : (output_l = (join_words_z_143 (selected)))) (PreH21 : (current_word_143 input i start cur )) (PreH22 : (prime_scan_state_143 l j isp )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((INT_MIN) <= (j * j )) ”
.

Definition words_in_sentence_safety_wit_27 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) <= l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((l <> (INT_MIN)) \/ (j <> (-1))) ” 
  &&  “ (j <> 0) ”
.

Definition words_in_sentence_safety_wit_28 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) <= l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_29 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((l % ( j ) ) = 0)) (PreH2 : ((j * j ) <= l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input i cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input i start cur )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_30 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((l % ( j ) ) = 0)) (PreH2 : ((j * j ) <= l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input i cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input i start cur )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> 0)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition words_in_sentence_safety_wit_31 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((l % ( j ) ) <> 0)) (PreH2 : ((j * j ) <= l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input i cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input i start cur )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition words_in_sentence_safety_wit_32 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_safety_wit_33 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (out_len > 0)) (PreH2 : ((j * j ) > l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input i cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input i start cur )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) (PreH29 : (isp <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition words_in_sentence_safety_wit_34 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (out_len > 0)) (PreH3 : ((j * j ) > l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input i cur words )) (PreH22 : (PrimeLengthWordsZ143 words selected )) (PreH23 : (output_l = (join_words_z_143 (selected)))) (PreH24 : (current_word_143 input i start cur )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) (PreH30 : (isp <> 0)) ,
  (CharArray.full out (out_len + 1 ) (app (output_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((out_len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + 1 )) ”
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (out_len > 0)) (PreH3 : ((j * j ) > l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input i cur words )) (PreH22 : (PrimeLengthWordsZ143 words selected )) (PreH23 : (output_l = (join_words_z_143 (selected)))) (PreH24 : (current_word_143 input i start cur )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) (PreH30 : (isp <> 0)) ,
  (CharArray.full out (out_len + 1 ) (app (output_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((out_len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + 1 )) ”
).

Definition words_in_sentence_safety_wit_34_split_goal_1 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (out_len > 0)) (PreH3 : ((j * j ) > l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input i cur words )) (PreH22 : (PrimeLengthWordsZ143 words selected )) (PreH23 : (output_l = (join_words_z_143 (selected)))) (PreH24 : (current_word_143 input i start cur )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) (PreH30 : (isp <> 0)) ,
  (CharArray.full out (out_len + 1 ) (app (output_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((out_len + 1 ) <= INT_MAX) ”
.

Definition words_in_sentence_safety_wit_34_split_goal_2 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (out_len > 0)) (PreH3 : ((j * j ) > l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input i cur words )) (PreH22 : (PrimeLengthWordsZ143 words selected )) (PreH23 : (output_l = (join_words_z_143 (selected)))) (PreH24 : (current_word_143 input i start cur )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) (PreH30 : (isp <> 0)) ,
  (CharArray.full out (out_len + 1 ) (app (output_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= (out_len + 1 )) ”
.

Definition words_in_sentence_safety_wit_35 := 
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur words )) (PreH25 : (PrimeLengthWordsZ143 words selected )) (PreH26 : (old_output = (join_words_z_143 (selected)))) (PreH27 : (current_word_143 input i start cur )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ ((out_len + l ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + l )) ”
.

Definition words_in_sentence_safety_wit_36 := 
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur words )) (PreH25 : (PrimeLengthWordsZ143 words selected )) (PreH26 : (old_output = (join_words_z_143 (selected)))) (PreH27 : (current_word_143 input i start cur )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + l ))
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_in_sentence_safety_wit_37 := 
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur words )) (PreH25 : (PrimeLengthWordsZ143 words selected )) (PreH26 : (old_output = (join_words_z_143 (selected)))) (PreH27 : (current_word_143 input i start cur )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + l ))
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_in_sentence_safety_wit_38 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp = 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_in_sentence_safety_wit_39 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp = 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_in_sentence_safety_wit_40 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_in_sentence_safety_wit_41 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_in_sentence_safety_wit_42 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur words )) (PreH25 : (PrimeLengthWordsZ143 words selected )) (PreH26 : (old_output = (join_words_z_143 (selected)))) (PreH27 : (current_word_143 input i start cur )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + l ))
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur words )) (PreH25 : (PrimeLengthWordsZ143 words selected )) (PreH26 : (old_output = (join_words_z_143 (selected)))) (PreH27 : (current_word_143 input i start cur )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + l ))
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition words_in_sentence_safety_wit_42_split_goal_1 := 
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur words )) (PreH25 : (PrimeLengthWordsZ143 words selected )) (PreH26 : (old_output = (join_words_z_143 (selected)))) (PreH27 : (current_word_143 input i start cur )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + l ))
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition words_in_sentence_safety_wit_42_split_goal_2 := 
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur words )) (PreH25 : (PrimeLengthWordsZ143 words selected )) (PreH26 : (old_output = (join_words_z_143 (selected)))) (PreH27 : (current_word_143 input i start cur )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + l ))
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_in_sentence_safety_wit_43 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp = 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp = 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition words_in_sentence_safety_wit_43_split_goal_1 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp = 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition words_in_sentence_safety_wit_43_split_goal_2 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input i cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input i start cur )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp = 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_in_sentence_safety_wit_44 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition words_in_sentence_safety_wit_44_split_goal_1 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition words_in_sentence_safety_wit_44_split_goal_2 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_in_sentence_safety_wit_45 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_in_sentence_safety_wit_46 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (i > n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n + 1 ))) (PreH4 : (0 <= out_len)) (PreH5 : (out_len <= i)) (PreH6 : (out_len <= n)) (PreH7 : (output_gap_outer_143 out_len start i )) (PreH8 : (outer_done_143 i n start )) (PreH9 : (out <> 0)) (PreH10 : (INT_MIN <= isp)) (PreH11 : (isp <= INT_MAX)) (PreH12 : (INT_MIN <= l)) (PreH13 : (l <= INT_MAX)) (PreH14 : (INT_MIN <= j)) (PreH15 : (j <= INT_MAX)) (PreH16 : ((Zlength (output_l)) = out_len)) (PreH17 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH18 : (PrimeLengthWordsZ143 words selected )) (PreH19 : (output_l = (join_words_z_143 (selected)))) (PreH20 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH21 : (n = (string_length (input)))) (PreH22 : (problem_143_pre_z input )) (PreH23 : (ascii_range_z_143 input )) (PreH24 : (valid_string input )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_in_sentence_entail_wit_1 := 
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (output_gap_outer_143 0 (-1) 0 ) ” 
  &&  “ (outer_done_143 0 retval (-1) ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = 0) ” 
  &&  “ (SentencePrefix143 input (min_z_143 (0) (retval)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 (0) (retval)) (-1) cur ) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  (store_string sentence_addr input )
  **  (CharArray.full retval_2 0 output_l )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
) \/
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (sentence_pre = sentence_addr)) (PreH5 : (problem_143_pre_z input )) (PreH6 : (ascii_range_z_143 input )) (PreH7 : (valid_string input )) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (sentence_pre = sentence_addr) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (output_gap_outer_143 0 (-1) 0 ) ” 
  &&  “ (outer_done_143 0 retval (-1) ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (SentencePrefix143 input (min_z_143 (0) (retval)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ ((@nil Z) = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 (0) (retval)) (-1) cur ) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
).

Definition words_in_sentence_entail_wit_2_1 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) < 2)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 0 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((i - start ) < 2)) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 0 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_2_2 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) < 2)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 0 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((i - start ) < 2)) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (i <= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n + 1 ))) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= i)) (PreH11 : (out_len <= n)) (PreH12 : (output_gap_outer_143 out_len start i )) (PreH13 : (outer_done_143 i n start )) (PreH14 : (out <> 0)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= l)) (PreH18 : (l <= INT_MAX)) (PreH19 : (INT_MIN <= j)) (PreH20 : (j <= INT_MAX)) (PreH21 : ((Zlength (output_l_2)) = out_len)) (PreH22 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH23 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH24 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH25 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 0 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_2_3 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) >= 2)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 1 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((i - start ) >= 2)) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 1 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_2_4 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : ((i - start ) >= 2)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 1 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((i - start ) >= 2)) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (i <= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n + 1 ))) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= i)) (PreH11 : (out_len <= n)) (PreH12 : (output_gap_outer_143 out_len start i )) (PreH13 : (outer_done_143 i n start )) (PreH14 : (out <> 0)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= l)) (PreH18 : (l <= INT_MAX)) (PreH19 : (INT_MIN <= j)) (PreH20 : (j <= INT_MAX)) (PreH21 : ((Zlength (output_l_2)) = out_len)) (PreH22 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH23 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH24 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH25 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 < (i - start )) ” 
  &&  “ ((i - start ) <= 100) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 12) ” 
  &&  “ (INT_MIN <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 (i - start ) 2 1 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_3_1 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((l % ( j ) ) = 0)) (PreH2 : ((j * j ) <= l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input i cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input i start cur_2 )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (l = (i - start )) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= 100) ” 
  &&  “ (2 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 12) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l (j + 1 ) 0 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((l % ( j ) ) = 0)) (PreH3 : ((j * j ) <= l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input i cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input i start cur_2 )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (l = (i - start )) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= 100) ” 
  &&  “ (2 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 12) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l (j + 1 ) 0 ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_3_2 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((l % ( j ) ) <> 0)) (PreH2 : ((j * j ) <= l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input i cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input i start cur_2 )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (l = (i - start )) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= 100) ” 
  &&  “ (2 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 12) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l (j + 1 ) isp ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((l % ( j ) ) <> 0)) (PreH3 : ((j * j ) <= l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input i cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input i start cur_2 )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (l = (i - start )) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= 100) ” 
  &&  “ (2 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 12) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l (j + 1 ) isp ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_4_1 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (out_len <= 0)) (PreH2 : ((j * j ) > l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input i cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input i start cur_2 )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) (PreH29 : (isp <> 0)) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (input_post: (@list Z))  (input_pre: (@list Z))  (output_pre: (@list Z))  (old_output: (@list Z))  (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ ((Zlength ((sublist (start) (i) (input)))) = l) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l < INT_MAX) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ ((out_len + l ) <= n) ” 
  &&  “ (output_gap_copy_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (isp <> 0) ” 
  &&  “ ((j * j ) > l) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (old_output = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l j isp ) ” 
  &&  “ (copy_prefix_143 old_output output_pre ) ” 
  &&  “ ((Zlength (output_pre)) = out_len) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ”
  &&  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_full (out + (out_len * sizeof(CHAR) ) ) l )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (out_len <= 0)) (PreH3 : ((j * j ) > l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input i cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input i start cur_2 )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) (PreH30 : (isp <> 0)) ,
  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ ((Zlength ((sublist (start) (i) (input)))) = l) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l < INT_MAX) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ ((out_len + l ) <= n) ” 
  &&  “ (output_gap_copy_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (isp <> 0) ” 
  &&  “ ((j * j ) > l) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l j isp ) ” 
  &&  “ (copy_prefix_143 (join_words_z_143 (selected)) output_l ) ” 
  &&  “ ((Zlength (output_l)) = out_len) ”
  &&  (CharArray.undef_full (out + (out_len * sizeof(CHAR) ) ) l )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start (sublist (0) (start) ((c_string (input)))) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.seg sentence_addr i (n + 1 ) (sublist (i) ((n + 1 )) ((c_string (input)))) )
).

Definition words_in_sentence_entail_wit_4_2 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (out_len > 0)) (PreH3 : ((j * j ) > l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input i cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input i start cur_2 )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) (PreH30 : (isp <> 0)) ,
  (CharArray.full out (out_len + 1 ) (app (output_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (input_post: (@list Z))  (input_pre: (@list Z))  (output_pre: (@list Z))  (old_output: (@list Z))  (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ ((Zlength ((sublist (start) (i) (input)))) = l) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l < INT_MAX) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= (out_len + 1 )) ” 
  &&  “ (((out_len + 1 ) + l ) <= n) ” 
  &&  “ (output_gap_copy_143 (out_len + 1 ) start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (isp <> 0) ” 
  &&  “ ((j * j ) > l) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (old_output = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l j isp ) ” 
  &&  “ (copy_prefix_143 old_output output_pre ) ” 
  &&  “ ((Zlength (output_pre)) = (out_len + 1 )) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ”
  &&  (CharArray.full out (out_len + 1 ) output_pre )
  **  (CharArray.undef_full (out + ((out_len + 1 ) * sizeof(CHAR) ) ) l )
  **  (CharArray.undef_seg out ((out_len + 1 ) + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (out_len > 0)) (PreH3 : ((j * j ) > l)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (l = (i - start ))) (PreH9 : (0 < l)) (PreH10 : (l <= 100)) (PreH11 : (2 <= j)) (PreH12 : (j <= 12)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (0 <= out_len)) (PreH16 : (out_len <= i)) (PreH17 : (output_gap_inner_143 out_len start )) (PreH18 : (word_boundary_143 input i n )) (PreH19 : (out <> 0)) (PreH20 : ((Zlength (output_l)) = out_len)) (PreH21 : (SentencePrefix143 input i cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input i start cur_2 )) (PreH25 : (prime_scan_state_143 l j isp )) (PreH26 : (n = (string_length (input)))) (PreH27 : (problem_143_pre_z input )) (PreH28 : (ascii_range_z_143 input )) (PreH29 : (valid_string input )) (PreH30 : (isp <> 0)) ,
  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ ((Zlength ((sublist (start) (i) (input)))) = l) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l < INT_MAX) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= (out_len + 1 )) ” 
  &&  “ (((out_len + 1 ) + l ) <= n) ” 
  &&  “ (output_gap_copy_143 (out_len + 1 ) start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (isp <> 0) ” 
  &&  “ ((j * j ) > l) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l j isp ) ” 
  &&  “ (copy_prefix_143 (join_words_z_143 (selected)) (app (output_l) ((cons (32) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (output_l) ((cons (32) ((@nil Z))))))) = (out_len + 1 )) ”
  &&  (CharArray.undef_full (out + ((out_len + 1 ) * sizeof(CHAR) ) ) l )
  **  (CharArray.undef_seg out ((out_len + 1 ) + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start (sublist (0) (start) ((c_string (input)))) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.seg sentence_addr i (n + 1 ) (sublist (i) ((n + 1 )) ((c_string (input)))) )
).

Definition words_in_sentence_entail_wit_5_1 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len i (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n i ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) i cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len i (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n i ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) i cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_5_2 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len start (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n start ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) start cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len start (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n start ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) start cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_5_3 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (selected_2: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur_2 words_2 )) (PreH25 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH26 : (old_output = (join_words_z_143 (selected_2)))) (PreH27 : (current_word_143 input i start cur_2 )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= (out_len + l )) ” 
  &&  “ ((out_len + l ) <= (i + 1 )) ” 
  &&  “ ((out_len + l ) <= n) ” 
  &&  “ (output_gap_outer_143 (out_len + l ) (-1) (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n (-1) ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = (out_len + l )) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) (-1) cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out (out_len + l ) output_l )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
) \/
(
forall (sentence_addr: Z) (input: (@list Z)) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (selected_2: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (out_len * sizeof(CHAR) ) ))) (PreH2 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH3 : (all_ascii (sublist (start) (i) (input)) )) (PreH4 : (0 <= l)) (PreH5 : (l < INT_MAX)) (PreH6 : (0 <= start)) (PreH7 : (start < i)) (PreH8 : (i <= n)) (PreH9 : (0 <= out_len)) (PreH10 : ((out_len + l ) <= n)) (PreH11 : (output_gap_copy_143 out_len start )) (PreH12 : (word_boundary_143 input i n )) (PreH13 : (isp <> 0)) (PreH14 : ((j * j ) > l)) (PreH15 : (INT_MIN <= isp)) (PreH16 : (isp <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (n = (string_length (input)))) (PreH21 : (problem_143_pre_z input )) (PreH22 : (ascii_range_z_143 input )) (PreH23 : (valid_string input )) (PreH24 : (SentencePrefix143 input i cur_2 words_2 )) (PreH25 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH26 : (old_output = (join_words_z_143 (selected_2)))) (PreH27 : (current_word_143 input i start cur_2 )) (PreH28 : (prime_scan_state_143 l j isp )) (PreH29 : (copy_prefix_143 old_output output_pre )) (PreH30 : ((Zlength (output_pre)) = out_len)) (PreH31 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH32 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full (out + (out_len * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= (out_len + l )) ” 
  &&  “ ((out_len + l ) <= (i + 1 )) ” 
  &&  “ ((out_len + l ) <= n) ” 
  &&  “ (output_gap_outer_143 (out_len + l ) (-1) (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n (-1) ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = (out_len + l )) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) (-1) cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (out_len + l ) (join_words_z_143 (selected)) )
).

Definition words_in_sentence_entail_wit_5_4 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : ((j * j ) > l)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (l = (i - start ))) (PreH7 : (0 < l)) (PreH8 : (l <= 100)) (PreH9 : (2 <= j)) (PreH10 : (j <= 12)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= i)) (PreH15 : (output_gap_inner_143 out_len start )) (PreH16 : (word_boundary_143 input i n )) (PreH17 : (out <> 0)) (PreH18 : ((Zlength (output_l_2)) = out_len)) (PreH19 : (SentencePrefix143 input i cur_2 words_2 )) (PreH20 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH21 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH22 : (current_word_143 input i start cur_2 )) (PreH23 : (prime_scan_state_143 l j isp )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) (PreH28 : (isp = 0)) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len (-1) (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n (-1) ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) (-1) cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((j * j ) > l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input i cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input i start cur_2 )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) (PreH29 : (isp = 0)) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len (-1) (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n (-1) ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) (-1) cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_5_5 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l_2)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH20 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH21 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len start (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n start ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) start cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len start (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n start ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) start cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_entail_wit_5_6 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= i)) (PreH9 : (out_len <= n)) (PreH10 : (output_gap_outer_143 out_len start i )) (PreH11 : (outer_done_143 i n start )) (PreH12 : (out <> 0)) (PreH13 : (INT_MIN <= isp)) (PreH14 : (isp <= INT_MAX)) (PreH15 : (INT_MIN <= l)) (PreH16 : (l <= INT_MAX)) (PreH17 : (INT_MIN <= j)) (PreH18 : (j <= INT_MAX)) (PreH19 : ((Zlength (output_l_2)) = out_len)) (PreH20 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH21 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH22 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH23 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH24 : (n = (string_length (input)))) (PreH25 : (problem_143_pre_z input )) (PreH26 : (ascii_range_z_143 input )) (PreH27 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z)))  (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len start (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n start ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) start cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
) \/
(
forall (input: (@list Z)) (selected_2: (@list (@list Z))) (cur_2: (@list Z)) (words_2: (@list (@list Z))) (output_l_2: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= i)) (PreH10 : (out_len <= n)) (PreH11 : (output_gap_outer_143 out_len start i )) (PreH12 : (outer_done_143 i n start )) (PreH13 : (out <> 0)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= l)) (PreH17 : (l <= INT_MAX)) (PreH18 : (INT_MIN <= j)) (PreH19 : (j <= INT_MAX)) (PreH20 : ((Zlength (output_l_2)) = out_len)) (PreH21 : (SentencePrefix143 input (min_z_143 (i) (n)) cur_2 words_2 )) (PreH22 : (PrimeLengthWordsZ143 words_2 selected_2 )) (PreH23 : (output_l_2 = (join_words_z_143 (selected_2)))) (PreH24 : (current_word_143 input (min_z_143 (i) (n)) start cur_2 )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) ,
  TT && emp 
|--
  EX (selected: (@list (@list Z)))  (cur: (@list Z))  (words: (@list (@list Z))) ,
  “ (output_l_2 = (join_words_z_143 (selected))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= (i + 1 )) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len start (i + 1 ) ) ” 
  &&  “ (outer_done_143 (i + 1 ) n start ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength ((join_words_z_143 (selected)))) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 ((i + 1 )) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (current_word_143 input (min_z_143 ((i + 1 )) (n)) start cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  emp
).

Definition words_in_sentence_return_wit_1 := 
(
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (0 <= out_len)) (PreH6 : (out_len <= i)) (PreH7 : (out_len <= n)) (PreH8 : (output_gap_outer_143 out_len start i )) (PreH9 : (outer_done_143 i n start )) (PreH10 : (out <> 0)) (PreH11 : (INT_MIN <= isp)) (PreH12 : (isp <= INT_MAX)) (PreH13 : (INT_MIN <= l)) (PreH14 : (l <= INT_MAX)) (PreH15 : (INT_MIN <= j)) (PreH16 : (j <= INT_MAX)) (PreH17 : ((Zlength (output_l)) = out_len)) (PreH18 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH19 : (PrimeLengthWordsZ143 words selected )) (PreH20 : (output_l = (join_words_z_143 (selected)))) (PreH21 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH22 : (n = (string_length (input)))) (PreH23 : (problem_143_pre_z input )) (PreH24 : (ascii_range_z_143 input )) (PreH25 : (valid_string input )) ,
  (CharArray.full out (out_len + 1 ) (app (output_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (problem_143_spec_z input output ) ”
  &&  (store_string sentence_addr input )
  **  (store_string out output )
  **  (CharArray.undef_seg out ((string_length (output)) + 1 ) ((string_length (input)) + 1 ) )
) \/
(
forall (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (0 <= (out_len + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (i > n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= i)) (PreH8 : (out_len <= n)) (PreH9 : (output_gap_outer_143 out_len start i )) (PreH10 : (outer_done_143 i n start )) (PreH11 : (out <> 0)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (INT_MIN <= l)) (PreH15 : (l <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : ((Zlength (output_l)) = out_len)) (PreH19 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH20 : (PrimeLengthWordsZ143 words selected )) (PreH21 : (output_l = (join_words_z_143 (selected)))) (PreH22 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH23 : (n = (string_length (input)))) (PreH24 : (problem_143_pre_z input )) (PreH25 : (ascii_range_z_143 input )) (PreH26 : (valid_string input )) ,
  (CharArray.full out (out_len + 1 ) (app (output_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (problem_143_spec_z input output ) ”
  &&  (CharArray.full out ((string_length (output)) + 1 ) (c_string (output)) )
  **  (CharArray.undef_seg out ((string_length (output)) + 1 ) ((string_length (input)) + 1 ) )
).

Definition words_in_sentence_partial_solve_wit_1_pure := 
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (PreH1 : (sentence_pre = sentence_addr)) (PreH2 : (problem_143_pre_z input )) (PreH3 : (ascii_range_z_143 input )) (PreH4 : (valid_string input )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  (store_string sentence_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
) \/
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (sentence_pre = sentence_addr)) (PreH3 : (problem_143_pre_z input )) (PreH4 : (ascii_range_z_143 input )) (PreH5 : (valid_string input )) ,
  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((string_length (input)) < INT_MAX) ”
).

Definition words_in_sentence_partial_solve_wit_1_pure_split_goal_1 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (sentence_pre = sentence_addr)) (PreH3 : (problem_143_pre_z input )) (PreH4 : (ascii_range_z_143 input )) (PreH5 : (valid_string input )) ,
  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((string_length (input)) < INT_MAX) ”
.

Definition words_in_sentence_partial_solve_wit_1_aux := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (PreH1 : (sentence_pre = sentence_addr)) (PreH2 : (problem_143_pre_z input )) (PreH3 : (ascii_range_z_143 input )) (PreH4 : (valid_string input )) ,
  (store_string sentence_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (sentence_pre = sentence_addr) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (store_string sentence_pre input )
.

Definition words_in_sentence_partial_solve_wit_1 := words_in_sentence_partial_solve_wit_1_pure -> words_in_sentence_partial_solve_wit_1_aux.

Definition words_in_sentence_partial_solve_wit_2_pure := 
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (sentence_pre = sentence_addr)) (PreH4 : (problem_143_pre_z input )) (PreH5 : (ascii_range_z_143 input )) (PreH6 : (valid_string input )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string sentence_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ”
) \/
(
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (sentence_pre = sentence_addr)) (PreH6 : (problem_143_pre_z input )) (PreH7 : (ascii_range_z_143 input )) (PreH8 : (valid_string input )) ,
  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (0 < (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= INT_MAX) ”
).

Definition words_in_sentence_partial_solve_wit_2_pure_split_goal_1 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (sentence_pre = sentence_addr)) (PreH6 : (problem_143_pre_z input )) (PreH7 : (ascii_range_z_143 input )) (PreH8 : (valid_string input )) ,
  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ (0 < (retval + 1 )) ”
.

Definition words_in_sentence_partial_solve_wit_2_pure_split_goal_2 := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (sentence_pre = sentence_addr)) (PreH6 : (problem_143_pre_z input )) (PreH7 : (ascii_range_z_143 input )) (PreH8 : (valid_string input )) ,
  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ”
.

Definition words_in_sentence_partial_solve_wit_2_aux := 
forall (sentence_pre: Z) (sentence_addr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (sentence_pre = sentence_addr)) (PreH4 : (problem_143_pre_z input )) (PreH5 : (ascii_range_z_143 input )) (PreH6 : (valid_string input )) ,
  (store_string sentence_pre input )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (sentence_pre = sentence_addr) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (CharArray.full sentence_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition words_in_sentence_partial_solve_wit_2 := words_in_sentence_partial_solve_wit_2_pure -> words_in_sentence_partial_solve_wit_2_aux.

Definition words_in_sentence_partial_solve_wit_3 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (out: Z) (out_len: Z) (isp: Z) (j: Z) (l: Z) (start: Z) (n: Z) (i: Z) (PreH1 : (out_len > 0)) (PreH2 : ((j * j ) > l)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (l = (i - start ))) (PreH8 : (0 < l)) (PreH9 : (l <= 100)) (PreH10 : (2 <= j)) (PreH11 : (j <= 12)) (PreH12 : (INT_MIN <= isp)) (PreH13 : (isp <= INT_MAX)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= i)) (PreH16 : (output_gap_inner_143 out_len start )) (PreH17 : (word_boundary_143 input i n )) (PreH18 : (out <> 0)) (PreH19 : ((Zlength (output_l)) = out_len)) (PreH20 : (SentencePrefix143 input i cur words )) (PreH21 : (PrimeLengthWordsZ143 words selected )) (PreH22 : (output_l = (join_words_z_143 (selected)))) (PreH23 : (current_word_143 input i start cur )) (PreH24 : (prime_scan_state_143 l j isp )) (PreH25 : (n = (string_length (input)))) (PreH26 : (problem_143_pre_z input )) (PreH27 : (ascii_range_z_143 input )) (PreH28 : (valid_string input )) (PreH29 : (isp <> 0)) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (out_len > 0) ” 
  &&  “ ((j * j ) > l) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (l = (i - start )) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= 100) ” 
  &&  “ (2 <= j) ” 
  &&  “ (j <= 12) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (output_gap_inner_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (out <> 0) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l j isp ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (isp <> 0) ”
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out out_len out_len (n + 1 ) )
  **  (CharArray.full out out_len output_l )
.

Definition words_in_sentence_partial_solve_wit_4_pure := 
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (PreH1 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH2 : (all_ascii (sublist (start) (i) (input)) )) (PreH3 : (0 <= l)) (PreH4 : (l < INT_MAX)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (i <= n)) (PreH8 : (0 <= out_len)) (PreH9 : ((out_len + l ) <= n)) (PreH10 : (output_gap_copy_143 out_len start )) (PreH11 : (word_boundary_143 input i n )) (PreH12 : (isp <> 0)) (PreH13 : ((j * j ) > l)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (out <> 0)) (PreH19 : (n = (string_length (input)))) (PreH20 : (problem_143_pre_z input )) (PreH21 : (ascii_range_z_143 input )) (PreH22 : (valid_string input )) (PreH23 : (SentencePrefix143 input i cur words )) (PreH24 : (PrimeLengthWordsZ143 words selected )) (PreH25 : (old_output = (join_words_z_143 (selected)))) (PreH26 : (current_word_143 input i start cur )) (PreH27 : (prime_scan_state_143 l j isp )) (PreH28 : (copy_prefix_143 old_output output_pre )) (PreH29 : ((Zlength (output_pre)) = out_len)) (PreH30 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH31 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_addr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_full (out + (out_len * sizeof(CHAR) ) ) l )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = l) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l < INT_MAX) ”
.

Definition words_in_sentence_partial_solve_wit_4_aux := 
forall (sentence_addr: Z) (input: (@list Z)) (cur: (@list Z)) (words: (@list (@list Z))) (selected: (@list (@list Z))) (old_output: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_pre: (@list Z)) (i: Z) (start: Z) (l: Z) (n: Z) (out_len: Z) (isp: Z) (j: Z) (out: Z) (PreH1 : ((Zlength ((sublist (start) (i) (input)))) = l)) (PreH2 : (all_ascii (sublist (start) (i) (input)) )) (PreH3 : (0 <= l)) (PreH4 : (l < INT_MAX)) (PreH5 : (0 <= start)) (PreH6 : (start < i)) (PreH7 : (i <= n)) (PreH8 : (0 <= out_len)) (PreH9 : ((out_len + l ) <= n)) (PreH10 : (output_gap_copy_143 out_len start )) (PreH11 : (word_boundary_143 input i n )) (PreH12 : (isp <> 0)) (PreH13 : ((j * j ) > l)) (PreH14 : (INT_MIN <= isp)) (PreH15 : (isp <= INT_MAX)) (PreH16 : (INT_MIN <= j)) (PreH17 : (j <= INT_MAX)) (PreH18 : (out <> 0)) (PreH19 : (n = (string_length (input)))) (PreH20 : (problem_143_pre_z input )) (PreH21 : (ascii_range_z_143 input )) (PreH22 : (valid_string input )) (PreH23 : (SentencePrefix143 input i cur words )) (PreH24 : (PrimeLengthWordsZ143 words selected )) (PreH25 : (old_output = (join_words_z_143 (selected)))) (PreH26 : (current_word_143 input i start cur )) (PreH27 : (prime_scan_state_143 l j isp )) (PreH28 : (copy_prefix_143 old_output output_pre )) (PreH29 : ((Zlength (output_pre)) = out_len)) (PreH30 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH31 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) ,
  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_full (out + (out_len * sizeof(CHAR) ) ) l )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
|--
  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = l) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l < INT_MAX) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = l) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l < INT_MAX) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ ((out_len + l ) <= n) ” 
  &&  “ (output_gap_copy_143 out_len start ) ” 
  &&  “ (word_boundary_143 input i n ) ” 
  &&  “ (isp <> 0) ” 
  &&  “ ((j * j ) > l) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (SentencePrefix143 input i cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (old_output = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input i start cur ) ” 
  &&  “ (prime_scan_state_143 l j isp ) ” 
  &&  “ (copy_prefix_143 old_output output_pre ) ” 
  &&  “ ((Zlength (output_pre)) = out_len) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ”
  &&  (CharArray.undef_full (out + (out_len * sizeof(CHAR) ) ) l )
  **  (CharArray.full (sentence_addr + (start * sizeof(CHAR) ) ) l (sublist (start) (i) (input)) )
  **  (CharArray.full out out_len output_pre )
  **  (CharArray.undef_seg out (out_len + l ) (n + 1 ) )
  **  (CharArray.seg sentence_addr 0 start input_pre )
  **  (CharArray.seg sentence_addr i (n + 1 ) input_post )
.

Definition words_in_sentence_partial_solve_wit_4 := words_in_sentence_partial_solve_wit_4_pure -> words_in_sentence_partial_solve_wit_4_aux.

Definition words_in_sentence_partial_solve_wit_5 := 
forall (sentence_addr: Z) (input: (@list Z)) (selected: (@list (@list Z))) (cur: (@list Z)) (words: (@list (@list Z))) (output_l: (@list Z)) (j: Z) (l: Z) (isp: Z) (out: Z) (start: Z) (out_len: Z) (n: Z) (i: Z) (PreH1 : (i > n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n + 1 ))) (PreH4 : (0 <= out_len)) (PreH5 : (out_len <= i)) (PreH6 : (out_len <= n)) (PreH7 : (output_gap_outer_143 out_len start i )) (PreH8 : (outer_done_143 i n start )) (PreH9 : (out <> 0)) (PreH10 : (INT_MIN <= isp)) (PreH11 : (isp <= INT_MAX)) (PreH12 : (INT_MIN <= l)) (PreH13 : (l <= INT_MAX)) (PreH14 : (INT_MIN <= j)) (PreH15 : (j <= INT_MAX)) (PreH16 : ((Zlength (output_l)) = out_len)) (PreH17 : (SentencePrefix143 input (min_z_143 (i) (n)) cur words )) (PreH18 : (PrimeLengthWordsZ143 words selected )) (PreH19 : (output_l = (join_words_z_143 (selected)))) (PreH20 : (current_word_143 input (min_z_143 (i) (n)) start cur )) (PreH21 : (n = (string_length (input)))) (PreH22 : (problem_143_pre_z input )) (PreH23 : (ascii_range_z_143 input )) (PreH24 : (valid_string input )) ,
  (store_string sentence_addr input )
  **  (CharArray.full out out_len output_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i > n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= i) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (output_gap_outer_143 out_len start i ) ” 
  &&  “ (outer_done_143 i n start ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (INT_MIN <= isp) ” 
  &&  “ (isp <= INT_MAX) ” 
  &&  “ (INT_MIN <= l) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (INT_MIN <= j) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ ((Zlength (output_l)) = out_len) ” 
  &&  “ (SentencePrefix143 input (min_z_143 (i) (n)) cur words ) ” 
  &&  “ (PrimeLengthWordsZ143 words selected ) ” 
  &&  “ (output_l = (join_words_z_143 (selected))) ” 
  &&  “ (current_word_143 input (min_z_143 (i) (n)) start cur ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (problem_143_pre_z input ) ” 
  &&  “ (ascii_range_z_143 input ) ” 
  &&  “ (valid_string input ) ”
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full sentence_addr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out out_len out_len (n + 1 ) )
  **  (CharArray.full out out_len output_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_words_in_sentence_safety_wit_1 : words_in_sentence_safety_wit_1.
Axiom proof_of_words_in_sentence_safety_wit_2 : words_in_sentence_safety_wit_2.
Axiom proof_of_words_in_sentence_safety_wit_3 : words_in_sentence_safety_wit_3.
Axiom proof_of_words_in_sentence_safety_wit_4 : words_in_sentence_safety_wit_4.
Axiom proof_of_words_in_sentence_safety_wit_5 : words_in_sentence_safety_wit_5.
Axiom proof_of_words_in_sentence_safety_wit_6 : words_in_sentence_safety_wit_6.
Axiom proof_of_words_in_sentence_safety_wit_7 : words_in_sentence_safety_wit_7.
Axiom proof_of_words_in_sentence_safety_wit_8 : words_in_sentence_safety_wit_8.
Axiom proof_of_words_in_sentence_safety_wit_9 : words_in_sentence_safety_wit_9.
Axiom proof_of_words_in_sentence_safety_wit_10 : words_in_sentence_safety_wit_10.
Axiom proof_of_words_in_sentence_safety_wit_11 : words_in_sentence_safety_wit_11.
Axiom proof_of_words_in_sentence_safety_wit_12 : words_in_sentence_safety_wit_12.
Axiom proof_of_words_in_sentence_safety_wit_13 : words_in_sentence_safety_wit_13.
Axiom proof_of_words_in_sentence_safety_wit_14 : words_in_sentence_safety_wit_14.
Axiom proof_of_words_in_sentence_safety_wit_15 : words_in_sentence_safety_wit_15.
Axiom proof_of_words_in_sentence_safety_wit_16 : words_in_sentence_safety_wit_16.
Axiom proof_of_words_in_sentence_safety_wit_17 : words_in_sentence_safety_wit_17.
Axiom proof_of_words_in_sentence_safety_wit_18 : words_in_sentence_safety_wit_18.
Axiom proof_of_words_in_sentence_safety_wit_19 : words_in_sentence_safety_wit_19.
Axiom proof_of_words_in_sentence_safety_wit_20 : words_in_sentence_safety_wit_20.
Axiom proof_of_words_in_sentence_safety_wit_21 : words_in_sentence_safety_wit_21.
Axiom proof_of_words_in_sentence_safety_wit_22 : words_in_sentence_safety_wit_22.
Axiom proof_of_words_in_sentence_safety_wit_23 : words_in_sentence_safety_wit_23.
Axiom proof_of_words_in_sentence_safety_wit_24 : words_in_sentence_safety_wit_24.
Axiom proof_of_words_in_sentence_safety_wit_25 : words_in_sentence_safety_wit_25.
Axiom proof_of_words_in_sentence_safety_wit_26 : words_in_sentence_safety_wit_26.
Axiom proof_of_words_in_sentence_safety_wit_27 : words_in_sentence_safety_wit_27.
Axiom proof_of_words_in_sentence_safety_wit_28 : words_in_sentence_safety_wit_28.
Axiom proof_of_words_in_sentence_safety_wit_29 : words_in_sentence_safety_wit_29.
Axiom proof_of_words_in_sentence_safety_wit_30 : words_in_sentence_safety_wit_30.
Axiom proof_of_words_in_sentence_safety_wit_31 : words_in_sentence_safety_wit_31.
Axiom proof_of_words_in_sentence_safety_wit_32 : words_in_sentence_safety_wit_32.
Axiom proof_of_words_in_sentence_safety_wit_33 : words_in_sentence_safety_wit_33.
Axiom proof_of_words_in_sentence_safety_wit_34 : words_in_sentence_safety_wit_34.
Axiom proof_of_words_in_sentence_safety_wit_35 : words_in_sentence_safety_wit_35.
Axiom proof_of_words_in_sentence_safety_wit_36 : words_in_sentence_safety_wit_36.
Axiom proof_of_words_in_sentence_safety_wit_37 : words_in_sentence_safety_wit_37.
Axiom proof_of_words_in_sentence_safety_wit_38 : words_in_sentence_safety_wit_38.
Axiom proof_of_words_in_sentence_safety_wit_39 : words_in_sentence_safety_wit_39.
Axiom proof_of_words_in_sentence_safety_wit_40 : words_in_sentence_safety_wit_40.
Axiom proof_of_words_in_sentence_safety_wit_41 : words_in_sentence_safety_wit_41.
Axiom proof_of_words_in_sentence_safety_wit_42 : words_in_sentence_safety_wit_42.
Axiom proof_of_words_in_sentence_safety_wit_43 : words_in_sentence_safety_wit_43.
Axiom proof_of_words_in_sentence_safety_wit_44 : words_in_sentence_safety_wit_44.
Axiom proof_of_words_in_sentence_safety_wit_45 : words_in_sentence_safety_wit_45.
Axiom proof_of_words_in_sentence_safety_wit_46 : words_in_sentence_safety_wit_46.
Axiom proof_of_words_in_sentence_entail_wit_1 : words_in_sentence_entail_wit_1.
Axiom proof_of_words_in_sentence_entail_wit_2_1 : words_in_sentence_entail_wit_2_1.
Axiom proof_of_words_in_sentence_entail_wit_2_2 : words_in_sentence_entail_wit_2_2.
Axiom proof_of_words_in_sentence_entail_wit_2_3 : words_in_sentence_entail_wit_2_3.
Axiom proof_of_words_in_sentence_entail_wit_2_4 : words_in_sentence_entail_wit_2_4.
Axiom proof_of_words_in_sentence_entail_wit_3_1 : words_in_sentence_entail_wit_3_1.
Axiom proof_of_words_in_sentence_entail_wit_3_2 : words_in_sentence_entail_wit_3_2.
Axiom proof_of_words_in_sentence_entail_wit_4_1 : words_in_sentence_entail_wit_4_1.
Axiom proof_of_words_in_sentence_entail_wit_4_2 : words_in_sentence_entail_wit_4_2.
Axiom proof_of_words_in_sentence_entail_wit_5_1 : words_in_sentence_entail_wit_5_1.
Axiom proof_of_words_in_sentence_entail_wit_5_2 : words_in_sentence_entail_wit_5_2.
Axiom proof_of_words_in_sentence_entail_wit_5_3 : words_in_sentence_entail_wit_5_3.
Axiom proof_of_words_in_sentence_entail_wit_5_4 : words_in_sentence_entail_wit_5_4.
Axiom proof_of_words_in_sentence_entail_wit_5_5 : words_in_sentence_entail_wit_5_5.
Axiom proof_of_words_in_sentence_entail_wit_5_6 : words_in_sentence_entail_wit_5_6.
Axiom proof_of_words_in_sentence_return_wit_1 : words_in_sentence_return_wit_1.
Axiom proof_of_words_in_sentence_partial_solve_wit_1_pure : words_in_sentence_partial_solve_wit_1_pure.
Axiom proof_of_words_in_sentence_partial_solve_wit_1 : words_in_sentence_partial_solve_wit_1.
Axiom proof_of_words_in_sentence_partial_solve_wit_2_pure : words_in_sentence_partial_solve_wit_2_pure.
Axiom proof_of_words_in_sentence_partial_solve_wit_2 : words_in_sentence_partial_solve_wit_2.
Axiom proof_of_words_in_sentence_partial_solve_wit_3 : words_in_sentence_partial_solve_wit_3.
Axiom proof_of_words_in_sentence_partial_solve_wit_4_pure : words_in_sentence_partial_solve_wit_4_pure.
Axiom proof_of_words_in_sentence_partial_solve_wit_4 : words_in_sentence_partial_solve_wit_4.
Axiom proof_of_words_in_sentence_partial_solve_wit_5 : words_in_sentence_partial_solve_wit_5.

End VC_Correct.
