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
Require Import coins_118.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function is_vowel_code_118 -----*)

Definition is_vowel_code_118_safety_wit_1 := 
forall (ch_pre: Z) (PreH1 : (0 <= ch_pre)) (PreH2 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition is_vowel_code_118_safety_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 65)) (PreH2 : (0 <= ch_pre)) (PreH3 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 65)) (PreH2 : (0 <= ch_pre)) (PreH3 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition is_vowel_code_118_safety_wit_4 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_5 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition is_vowel_code_118_safety_wit_6 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_7 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (79 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 79) ”
.

Definition is_vowel_code_118_safety_wit_8 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_9 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (85 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 85) ”
.

Definition is_vowel_code_118_safety_wit_10 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_11 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_vowel_code_118_safety_wit_12 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_13 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition is_vowel_code_118_safety_wit_14 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_15 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (105 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 105) ”
.

Definition is_vowel_code_118_safety_wit_16 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (0 <= ch_pre)) (PreH10 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_17 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (0 <= ch_pre)) (PreH10 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition is_vowel_code_118_safety_wit_18 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (0 <= ch_pre)) (PreH11 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_19 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (0 <= ch_pre)) (PreH11 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition is_vowel_code_118_safety_wit_20 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_118_safety_wit_21 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_vowel_code_118_return_wit_1 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (0 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (0 <= ch_pre)) (PreH11 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_4 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (0 <= ch_pre)) (PreH10 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_5 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_6 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_7 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_8 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_9 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_10 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_118_return_wit_11 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 65)) (PreH2 : (0 <= ch_pre)) (PreH3 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel_z_118 ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel_z_118 ch_pre ) ”
  &&  emp)
.

(*----- Function get_closest_vowel -----*)

Definition get_closest_vowel_safety_wit_1 := 
forall (word_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (all_ascii input )) (PreH5 : (problem_118_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string word_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_2 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (valid_string input )) (PreH4 : (all_ascii input )) (PreH5 : (problem_118_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : (alpha_codes_z_118 input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition get_closest_vowel_safety_wit_3 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n < 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_4 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (n < 3)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (valid_string input )) (PreH7 : (all_ascii input )) (PreH8 : (problem_118_pre_z input )) (PreH9 : (ascii_range_z input )) (PreH10 : (alpha_codes_z_118 input )) (PreH11 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_5 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n < 3)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_6 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n < 3)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_7 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n < 3)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_8 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_9 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_10 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_11 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "cur_vowel" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_12 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "right_vowel" ) )) # Int  |->_)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_13 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_14 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ ((n - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 2 )) ”
.

Definition get_closest_vowel_safety_wit_15 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_closest_vowel_safety_wit_16 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (right: Z) (cur: Z) (out: Z) (n: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (3 <= n)) (PreH4 : (n < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n - 2 ))) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_17 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (right: Z) (out: Z) (n: Z) (PreH1 : (i >= 1)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_closest_vowel_safety_wit_18 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (right: Z) (out: Z) (n: Z) (PreH1 : (i >= 1)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_19 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (out: Z) (n: Z) (PreH1 : (i >= 1)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition get_closest_vowel_safety_wit_20 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (out: Z) (n: Z) (PreH1 : (i >= 1)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_21 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ~((is_vowel_z_118 (Znth i (c_string (input)) 0) ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (i >= 1)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_22 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (i >= 1)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_23 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = 0)) (PreH3 : ~((is_vowel_z_118 (Znth i (c_string (input)) 0) ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (i >= 1)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out = 0)) (PreH8 : (3 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n - 2 ))) (PreH12 : (valid_string input )) (PreH13 : (all_ascii input )) (PreH14 : (problem_118_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : (alpha_codes_z_118 input )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_24 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = 1)) (PreH3 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (i >= 1)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out = 0)) (PreH8 : (3 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n - 2 ))) (PreH12 : (valid_string input )) (PreH13 : (all_ascii input )) (PreH14 : (problem_118_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : (alpha_codes_z_118 input )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_25 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH3 : (retval = 1)) (PreH4 : (retval = 1)) (PreH5 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (i >= 1)) (PreH8 : (n = (string_length (input)))) (PreH9 : (out = 0)) (PreH10 : (3 <= n)) (PreH11 : (n < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= (n - 2 ))) (PreH14 : (valid_string input )) (PreH15 : (all_ascii input )) (PreH16 : (problem_118_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : (alpha_codes_z_118 input )) (PreH19 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_26 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) )) (PreH3 : (retval = 1)) (PreH4 : (retval = 1)) (PreH5 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (i >= 1)) (PreH8 : (n = (string_length (input)))) (PreH9 : (out = 0)) (PreH10 : (3 <= n)) (PreH11 : (n < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= (n - 2 ))) (PreH14 : (valid_string input )) (PreH15 : (all_ascii input )) (PreH16 : (problem_118_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : (alpha_codes_z_118 input )) (PreH19 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_27 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH4 : (retval = 1)) (PreH5 : (retval = 1)) (PreH6 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH7 : (0 <= ((string_length (input)) + 1 ))) (PreH8 : (i >= 1)) (PreH9 : (n = (string_length (input)))) (PreH10 : (out = 0)) (PreH11 : (3 <= n)) (PreH12 : (n < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n - 2 ))) (PreH15 : (valid_string input )) (PreH16 : (all_ascii input )) (PreH17 : (problem_118_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : (alpha_codes_z_118 input )) (PreH20 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_28 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) )) (PreH4 : (retval = 1)) (PreH5 : (retval = 1)) (PreH6 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH7 : (0 <= ((string_length (input)) + 1 ))) (PreH8 : (i >= 1)) (PreH9 : (n = (string_length (input)))) (PreH10 : (out = 0)) (PreH11 : (3 <= n)) (PreH12 : (n < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n - 2 ))) (PreH15 : (valid_string input )) (PreH16 : (all_ascii input )) (PreH17 : (problem_118_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : (alpha_codes_z_118 input )) (PreH20 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_29 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ~((is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) ))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_2 = 0)) (PreH5 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH6 : (retval = 1)) (PreH7 : (retval = 1)) (PreH8 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH9 : (0 <= ((string_length (input)) + 1 ))) (PreH10 : (i >= 1)) (PreH11 : (n = (string_length (input)))) (PreH12 : (out = 0)) (PreH13 : (3 <= n)) (PreH14 : (n < INT_MAX)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n - 2 ))) (PreH17 : (valid_string input )) (PreH18 : (all_ascii input )) (PreH19 : (problem_118_pre_z input )) (PreH20 : (ascii_range_z input )) (PreH21 : (alpha_codes_z_118 input )) (PreH22 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_30 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) )) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_2 = 0)) (PreH5 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH6 : (retval = 1)) (PreH7 : (retval = 1)) (PreH8 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH9 : (0 <= ((string_length (input)) + 1 ))) (PreH10 : (i >= 1)) (PreH11 : (n = (string_length (input)))) (PreH12 : (out = 0)) (PreH13 : (3 <= n)) (PreH14 : (n < INT_MAX)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n - 2 ))) (PreH17 : (valid_string input )) (PreH18 : (all_ascii input )) (PreH19 : (problem_118_pre_z input )) (PreH20 : (ascii_range_z input )) (PreH21 : (alpha_codes_z_118 input )) (PreH22 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_31 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) ))) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_32 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) )) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_33 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (cur = (Znth (i) (input) (0)))) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (closest_vowel_candidate_z_118 input i )) (PreH14 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  (store_string word_pre input )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_closest_vowel_safety_wit_34 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (out = 0)) (PreH5 : (cur = (Znth (i) (input) (0)))) (PreH6 : (3 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n - 2 ))) (PreH10 : (valid_string input )) (PreH11 : (all_ascii input )) (PreH12 : (problem_118_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : (alpha_codes_z_118 input )) (PreH15 : (closest_vowel_candidate_z_118 input i )) (PreH16 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_full retval 2 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_35 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_full retval 2 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_36 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_full retval 2 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_37 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits (cur) (8)))
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_38 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits (cur) (8)))
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_39 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (3 <= n)) (PreH4 : (n < INT_MAX)) (PreH5 : (1 <= i)) (PreH6 : (i <= (n - 2 ))) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ~((closest_vowel_candidate_z_118 input i ))) (PreH13 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition get_closest_vowel_safety_wit_40 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (3 <= n)) (PreH4 : (n < INT_MAX)) (PreH5 : (1 <= i)) (PreH6 : (i <= (n - 2 ))) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ~((closest_vowel_candidate_z_118 input i ))) (PreH13 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_41 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (i = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : (no_candidate_after_z_118 input 0 )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_closest_vowel_safety_wit_42 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (out = 0)) (PreH5 : (i = 0)) (PreH6 : (valid_string input )) (PreH7 : (all_ascii input )) (PreH8 : (problem_118_pre_z input )) (PreH9 : (ascii_range_z input )) (PreH10 : (alpha_codes_z_118 input )) (PreH11 : (no_candidate_after_z_118 input 0 )) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_43 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (i = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : (no_candidate_after_z_118 input 0 )) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition get_closest_vowel_safety_wit_44 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (i = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : (no_candidate_after_z_118 input 0 )) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_safety_wit_45 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (i = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : (no_candidate_after_z_118 input 0 )) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_closest_vowel_entail_wit_1 := 
(
forall (word_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (all_ascii input )) (PreH5 : (problem_118_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) ,
  (store_string word_pre input )
|--
  “ (retval = (string_length (input))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (all_ascii input )) (PreH5 : (problem_118_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (alpha_codes_z_118 input ) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (all_ascii input )) (PreH5 : (problem_118_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (alpha_codes_z_118 input ) ”
.

Definition get_closest_vowel_entail_wit_2 := 
(
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n >= 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  (store_string word_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= (n - 2 )) ” 
  &&  “ ((n - 2 ) <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input (n - 2 ) ) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (n >= 3)) (PreH3 : (n = (string_length (input)))) (PreH4 : (out = 0)) (PreH5 : (valid_string input )) (PreH6 : (all_ascii input )) (PreH7 : (problem_118_pre_z input )) (PreH8 : (ascii_range_z input )) (PreH9 : (alpha_codes_z_118 input )) (PreH10 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (no_candidate_after_z_118 input (n - 2 ) ) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_2_split_goal_1 := 
forall (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (n >= 3)) (PreH3 : (n = (string_length (input)))) (PreH4 : (out = 0)) (PreH5 : (valid_string input )) (PreH6 : (all_ascii input )) (PreH7 : (problem_118_pre_z input )) (PreH8 : (ascii_range_z input )) (PreH9 : (alpha_codes_z_118 input )) (PreH10 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (no_candidate_after_z_118 input (n - 2 ) ) ”
.

Definition get_closest_vowel_entail_wit_3 := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) ))) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ ((Znth i (c_string (input)) 0) = (Znth (i) (input) (0))) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (closest_vowel_candidate_z_118 input i ) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) ))) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ (closest_vowel_candidate_z_118 input i ) ” 
  &&  “ ((Znth i (c_string (input)) 0) = (Znth (i) (input) (0))) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_3_split_goal_1 := 
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) ))) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ (closest_vowel_candidate_z_118 input i ) ”
.

Definition get_closest_vowel_entail_wit_3_split_goal_2 := 
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) ))) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (input)) 0) = (Znth (i) (input) (0))) ”
.

Definition get_closest_vowel_entail_wit_4_1 := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = 0)) (PreH3 : ~((is_vowel_z_118 (Znth i (c_string (input)) 0) ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (i >= 1)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out = 0)) (PreH8 : (3 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n - 2 ))) (PreH12 : (valid_string input )) (PreH13 : (all_ascii input )) (PreH14 : (problem_118_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : (alpha_codes_z_118 input )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ ~((closest_vowel_candidate_z_118 input i )) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = 0)) (PreH3 : ~((is_vowel_z_118 (Znth i (c_string (input)) 0) ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (i >= 1)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out = 0)) (PreH8 : (3 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n - 2 ))) (PreH12 : (valid_string input )) (PreH13 : (all_ascii input )) (PreH14 : (problem_118_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : (alpha_codes_z_118 input )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ ~((closest_vowel_candidate_z_118 input i )) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_4_1_split_goal_1 := 
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = 0)) (PreH3 : ~((is_vowel_z_118 (Znth i (c_string (input)) 0) ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (i >= 1)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out = 0)) (PreH8 : (3 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n - 2 ))) (PreH12 : (valid_string input )) (PreH13 : (all_ascii input )) (PreH14 : (problem_118_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : (alpha_codes_z_118 input )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ ~((closest_vowel_candidate_z_118 input i )) ”
.

Definition get_closest_vowel_entail_wit_4_2 := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) )) (PreH4 : (retval = 1)) (PreH5 : (retval = 1)) (PreH6 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH7 : (0 <= ((string_length (input)) + 1 ))) (PreH8 : (i >= 1)) (PreH9 : (n = (string_length (input)))) (PreH10 : (out = 0)) (PreH11 : (3 <= n)) (PreH12 : (n < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n - 2 ))) (PreH15 : (valid_string input )) (PreH16 : (all_ascii input )) (PreH17 : (problem_118_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : (alpha_codes_z_118 input )) (PreH20 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ ~((closest_vowel_candidate_z_118 input i )) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) )) (PreH4 : (retval = 1)) (PreH5 : (retval = 1)) (PreH6 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH7 : (0 <= ((string_length (input)) + 1 ))) (PreH8 : (i >= 1)) (PreH9 : (n = (string_length (input)))) (PreH10 : (out = 0)) (PreH11 : (3 <= n)) (PreH12 : (n < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n - 2 ))) (PreH15 : (valid_string input )) (PreH16 : (all_ascii input )) (PreH17 : (problem_118_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : (alpha_codes_z_118 input )) (PreH20 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ ~((closest_vowel_candidate_z_118 input i )) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_4_2_split_goal_1 := 
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) )) (PreH4 : (retval = 1)) (PreH5 : (retval = 1)) (PreH6 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH7 : (0 <= ((string_length (input)) + 1 ))) (PreH8 : (i >= 1)) (PreH9 : (n = (string_length (input)))) (PreH10 : (out = 0)) (PreH11 : (3 <= n)) (PreH12 : (n < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n - 2 ))) (PreH15 : (valid_string input )) (PreH16 : (all_ascii input )) (PreH17 : (problem_118_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : (alpha_codes_z_118 input )) (PreH20 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ ~((closest_vowel_candidate_z_118 input i )) ”
.

Definition get_closest_vowel_entail_wit_4_3 := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) )) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ ~((closest_vowel_candidate_z_118 input i )) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) )) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ ~((closest_vowel_candidate_z_118 input i )) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_4_3_split_goal_1 := 
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 1)) (PreH3 : (is_vowel_z_118 (Znth (i - 1 ) (c_string (input)) 0) )) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH7 : (retval = 1)) (PreH8 : (retval = 1)) (PreH9 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH10 : (0 <= ((string_length (input)) + 1 ))) (PreH11 : (i >= 1)) (PreH12 : (n = (string_length (input)))) (PreH13 : (out = 0)) (PreH14 : (3 <= n)) (PreH15 : (n < INT_MAX)) (PreH16 : (0 <= i)) (PreH17 : (i <= (n - 2 ))) (PreH18 : (valid_string input )) (PreH19 : (all_ascii input )) (PreH20 : (problem_118_pre_z input )) (PreH21 : (ascii_range_z input )) (PreH22 : (alpha_codes_z_118 input )) (PreH23 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ ~((closest_vowel_candidate_z_118 input i )) ”
.

Definition get_closest_vowel_entail_wit_5 := 
(
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (i: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (3 <= n)) (PreH4 : (n < INT_MAX)) (PreH5 : (1 <= i)) (PreH6 : (i <= (n - 2 ))) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ~((closest_vowel_candidate_z_118 input i ))) (PreH13 : (no_candidate_after_z_118 input i )) ,
  (store_string word_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input (i - 1 ) ) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (n: Z) (out: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : ~((closest_vowel_candidate_z_118 input i ))) (PreH14 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ (no_candidate_after_z_118 input (i - 1 ) ) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_5_split_goal_1 := 
forall (input: (@list Z)) (n: Z) (out: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : ~((closest_vowel_candidate_z_118 input i ))) (PreH14 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ (no_candidate_after_z_118 input (i - 1 ) ) ”
.

Definition get_closest_vowel_entail_wit_6 := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (PreH1 : (i < 1)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (no_candidate_after_z_118 input i )) ,
  (store_string word_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input 0 ) ”
  &&  (store_string word_pre input )
) \/
(
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < 1)) (PreH3 : (n = (string_length (input)))) (PreH4 : (out = 0)) (PreH5 : (3 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n - 2 ))) (PreH9 : (valid_string input )) (PreH10 : (all_ascii input )) (PreH11 : (problem_118_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : (alpha_codes_z_118 input )) (PreH14 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ (no_candidate_after_z_118 input 0 ) ”
  &&  emp
).

Definition get_closest_vowel_entail_wit_6_split_goal_1 := 
forall (input: (@list Z)) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < 1)) (PreH3 : (n = (string_length (input)))) (PreH4 : (out = 0)) (PreH5 : (3 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n - 2 ))) (PreH9 : (valid_string input )) (PreH10 : (all_ascii input )) (PreH11 : (problem_118_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : (alpha_codes_z_118 input )) (PreH14 : (no_candidate_after_z_118 input i )) ,
  TT && emp 
|--
  “ (no_candidate_after_z_118 input 0 ) ”
.

Definition get_closest_vowel_return_wit_1 := 
(
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (i = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : (no_candidate_after_z_118 input 0 )) ,
  (CharArray.undef_seg retval (0 + 1 ) 1 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_118_spec_z input output ) ”
  &&  (store_string word_pre input )
  **  (store_string retval output )
) \/
(
forall (input: (@list Z)) (n: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (i = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : (no_candidate_after_z_118 input 0 )) ,
  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 0)
|--
  EX (output: (@list Z)) ,
  “ (problem_118_spec_z input output ) ”
  &&  (CharArray.full retval ((string_length (output)) + 1 ) (c_string (output)) )
).

Definition get_closest_vowel_return_wit_2 := 
(
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_seg retval (1 + 1 ) 2 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits (cur) (8)))
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_118_spec_z input output ) ”
  &&  (store_string word_pre input )
  **  (store_string retval output )
) \/
(
forall (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits (cur) (8)))
|--
  EX (output: (@list Z)) ,
  “ (problem_118_spec_z input output ) ”
  &&  (CharArray.full retval ((string_length (output)) + 1 ) (c_string (output)) )
).

Definition get_closest_vowel_return_wit_3 := 
(
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n < 3)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_seg retval (0 + 1 ) 1 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_118_spec_z input output ) ”
  &&  (store_string word_pre input )
  **  (store_string retval output )
) \/
(
forall (input: (@list Z)) (n: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n < 3)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 0)
|--
  EX (output: (@list Z)) ,
  “ (problem_118_spec_z input output ) ”
  &&  (CharArray.full retval ((string_length (output)) + 1 ) (c_string (output)) )
).

Definition get_closest_vowel_partial_solve_wit_1_pure := 
forall (word_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (all_ascii input )) (PreH3 : (problem_118_pre_z input )) (PreH4 : (ascii_range_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  (store_string word_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition get_closest_vowel_partial_solve_wit_1_aux := 
forall (word_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (all_ascii input )) (PreH3 : (problem_118_pre_z input )) (PreH4 : (ascii_range_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  (store_string word_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string word_pre input )
.

Definition get_closest_vowel_partial_solve_wit_1 := get_closest_vowel_partial_solve_wit_1_pure -> get_closest_vowel_partial_solve_wit_1_aux.

Definition get_closest_vowel_partial_solve_wit_2_pure := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n < 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (store_string word_pre input )
|--
  “ (1 > 0) ” 
  &&  “ (1 < INT_MAX) ”
.

Definition get_closest_vowel_partial_solve_wit_2_aux := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (PreH1 : (n < 3)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : ((string_length (input)) < INT_MAX)) ,
  (store_string word_pre input )
|--
  “ (1 > 0) ” 
  &&  “ (1 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n < 3) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_2 := get_closest_vowel_partial_solve_wit_2_pure -> get_closest_vowel_partial_solve_wit_2_aux.

Definition get_closest_vowel_partial_solve_wit_3 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n < 3)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n < 3) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_4_pure := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (out: Z) (n: Z) (PreH1 : (i >= 1)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ ((Znth i (c_string (input)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ”
) \/
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (out: Z) (n: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (right_vowel <= INT_MAX)) (PreH4 : (cur_vowel <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (right_vowel >= INT_MIN)) (PreH12 : (cur_vowel >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (0 <= ((string_length (input)) + 1 ))) (PreH18 : (i >= 1)) (PreH19 : (n = (string_length (input)))) (PreH20 : (out = 0)) (PreH21 : (3 <= n)) (PreH22 : (n < INT_MAX)) (PreH23 : (0 <= i)) (PreH24 : (i <= (n - 2 ))) (PreH25 : (valid_string input )) (PreH26 : (all_ascii input )) (PreH27 : (problem_118_pre_z input )) (PreH28 : (ascii_range_z input )) (PreH29 : (alpha_codes_z_118 input )) (PreH30 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 127) ”
).

Definition get_closest_vowel_partial_solve_wit_4_pure_split_goal_1 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (out: Z) (n: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (right_vowel <= INT_MAX)) (PreH4 : (cur_vowel <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (right_vowel >= INT_MIN)) (PreH12 : (cur_vowel >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (0 <= ((string_length (input)) + 1 ))) (PreH18 : (i >= 1)) (PreH19 : (n = (string_length (input)))) (PreH20 : (out = 0)) (PreH21 : (3 <= n)) (PreH22 : (n < INT_MAX)) (PreH23 : (0 <= i)) (PreH24 : (i <= (n - 2 ))) (PreH25 : (valid_string input )) (PreH26 : (all_ascii input )) (PreH27 : (problem_118_pre_z input )) (PreH28 : (ascii_range_z input )) (PreH29 : (alpha_codes_z_118 input )) (PreH30 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= (Znth i (c_string (input)) 0)) ”
.

Definition get_closest_vowel_partial_solve_wit_4_pure_split_goal_2 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (out: Z) (n: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (right_vowel <= INT_MAX)) (PreH4 : (cur_vowel <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (right_vowel >= INT_MIN)) (PreH12 : (cur_vowel >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (0 <= ((string_length (input)) + 1 ))) (PreH18 : (i >= 1)) (PreH19 : (n = (string_length (input)))) (PreH20 : (out = 0)) (PreH21 : (3 <= n)) (PreH22 : (n < INT_MAX)) (PreH23 : (0 <= i)) (PreH24 : (i <= (n - 2 ))) (PreH25 : (valid_string input )) (PreH26 : (all_ascii input )) (PreH27 : (problem_118_pre_z input )) (PreH28 : (ascii_range_z input )) (PreH29 : (alpha_codes_z_118 input )) (PreH30 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((Znth i (c_string (input)) 0) <= 127) ”
.

Definition get_closest_vowel_partial_solve_wit_4_aux := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (PreH1 : (i >= 1)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out = 0)) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (no_candidate_after_z_118 input i )) ,
  (store_string word_pre input )
|--
  “ ((Znth i (c_string (input)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_4 := get_closest_vowel_partial_solve_wit_4_pure -> get_closest_vowel_partial_solve_wit_4_aux.

Definition get_closest_vowel_partial_solve_wit_5_pure := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = 1)) (PreH3 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (i >= 1)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out = 0)) (PreH8 : (3 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n - 2 ))) (PreH12 : (valid_string input )) (PreH13 : (all_ascii input )) (PreH14 : (problem_118_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : (alpha_codes_z_118 input )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((Znth (i + 1 ) (c_string (input)) 0) <= 127) ” 
  &&  “ (0 <= (Znth (i + 1 ) (c_string (input)) 0)) ”
) \/
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (right_vowel <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (right_vowel >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (retval = 1)) (PreH18 : (retval = 1)) (PreH19 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH20 : (0 <= ((string_length (input)) + 1 ))) (PreH21 : (i >= 1)) (PreH22 : (n = (string_length (input)))) (PreH23 : (out = 0)) (PreH24 : (3 <= n)) (PreH25 : (n < INT_MAX)) (PreH26 : (0 <= i)) (PreH27 : (i <= (n - 2 ))) (PreH28 : (valid_string input )) (PreH29 : (all_ascii input )) (PreH30 : (problem_118_pre_z input )) (PreH31 : (ascii_range_z input )) (PreH32 : (alpha_codes_z_118 input )) (PreH33 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= (Znth (i + 1 ) (c_string (input)) 0)) ” 
  &&  “ ((Znth (i + 1 ) (c_string (input)) 0) <= 127) ”
).

Definition get_closest_vowel_partial_solve_wit_5_pure_split_goal_1 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (right_vowel <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (right_vowel >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (retval = 1)) (PreH18 : (retval = 1)) (PreH19 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH20 : (0 <= ((string_length (input)) + 1 ))) (PreH21 : (i >= 1)) (PreH22 : (n = (string_length (input)))) (PreH23 : (out = 0)) (PreH24 : (3 <= n)) (PreH25 : (n < INT_MAX)) (PreH26 : (0 <= i)) (PreH27 : (i <= (n - 2 ))) (PreH28 : (valid_string input )) (PreH29 : (all_ascii input )) (PreH30 : (problem_118_pre_z input )) (PreH31 : (ascii_range_z input )) (PreH32 : (alpha_codes_z_118 input )) (PreH33 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= (Znth (i + 1 ) (c_string (input)) 0)) ”
.

Definition get_closest_vowel_partial_solve_wit_5_pure_split_goal_2 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (right_vowel <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (right_vowel >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (retval = 1)) (PreH18 : (retval = 1)) (PreH19 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH20 : (0 <= ((string_length (input)) + 1 ))) (PreH21 : (i >= 1)) (PreH22 : (n = (string_length (input)))) (PreH23 : (out = 0)) (PreH24 : (3 <= n)) (PreH25 : (n < INT_MAX)) (PreH26 : (0 <= i)) (PreH27 : (i <= (n - 2 ))) (PreH28 : (valid_string input )) (PreH29 : (all_ascii input )) (PreH30 : (problem_118_pre_z input )) (PreH31 : (ascii_range_z input )) (PreH32 : (alpha_codes_z_118 input )) (PreH33 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((Znth (i + 1 ) (c_string (input)) 0) <= 127) ”
.

Definition get_closest_vowel_partial_solve_wit_5_aux := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = 1)) (PreH3 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (i >= 1)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out = 0)) (PreH8 : (3 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n - 2 ))) (PreH12 : (valid_string input )) (PreH13 : (all_ascii input )) (PreH14 : (problem_118_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : (alpha_codes_z_118 input )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ ((Znth (i + 1 ) (c_string (input)) 0) <= 127) ” 
  &&  “ (0 <= (Znth (i + 1 ) (c_string (input)) 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel_z_118 (Znth i (c_string (input)) 0) ) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_5 := get_closest_vowel_partial_solve_wit_5_pure -> get_closest_vowel_partial_solve_wit_5_aux.

Definition get_closest_vowel_partial_solve_wit_6_pure := 
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH4 : (retval = 1)) (PreH5 : (retval = 1)) (PreH6 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH7 : (0 <= ((string_length (input)) + 1 ))) (PreH8 : (i >= 1)) (PreH9 : (n = (string_length (input)))) (PreH10 : (out = 0)) (PreH11 : (3 <= n)) (PreH12 : (n < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n - 2 ))) (PreH15 : (valid_string input )) (PreH16 : (all_ascii input )) (PreH17 : (problem_118_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : (alpha_codes_z_118 input )) (PreH20 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((Znth (i - 1 ) (c_string (input)) 0) <= 127) ” 
  &&  “ (0 <= (Znth (i - 1 ) (c_string (input)) 0)) ”
) \/
(
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (retval_2 <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (retval_2 >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (retval_2 = 0)) (PreH18 : (retval_2 = 0)) (PreH19 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH20 : (retval = 1)) (PreH21 : (retval = 1)) (PreH22 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH23 : (0 <= ((string_length (input)) + 1 ))) (PreH24 : (i >= 1)) (PreH25 : (n = (string_length (input)))) (PreH26 : (out = 0)) (PreH27 : (3 <= n)) (PreH28 : (n < INT_MAX)) (PreH29 : (0 <= i)) (PreH30 : (i <= (n - 2 ))) (PreH31 : (valid_string input )) (PreH32 : (all_ascii input )) (PreH33 : (problem_118_pre_z input )) (PreH34 : (ascii_range_z input )) (PreH35 : (alpha_codes_z_118 input )) (PreH36 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= (Znth (i - 1 ) (c_string (input)) 0)) ” 
  &&  “ ((Znth (i - 1 ) (c_string (input)) 0) <= 127) ”
).

Definition get_closest_vowel_partial_solve_wit_6_pure_split_goal_1 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (retval_2 <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (retval_2 >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (retval_2 = 0)) (PreH18 : (retval_2 = 0)) (PreH19 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH20 : (retval = 1)) (PreH21 : (retval = 1)) (PreH22 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH23 : (0 <= ((string_length (input)) + 1 ))) (PreH24 : (i >= 1)) (PreH25 : (n = (string_length (input)))) (PreH26 : (out = 0)) (PreH27 : (3 <= n)) (PreH28 : (n < INT_MAX)) (PreH29 : (0 <= i)) (PreH30 : (i <= (n - 2 ))) (PreH31 : (valid_string input )) (PreH32 : (all_ascii input )) (PreH33 : (problem_118_pre_z input )) (PreH34 : (ascii_range_z input )) (PreH35 : (alpha_codes_z_118 input )) (PreH36 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= (Znth (i - 1 ) (c_string (input)) 0)) ”
.

Definition get_closest_vowel_partial_solve_wit_6_pure_split_goal_2 := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (left_vowel: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (left_vowel <= INT_MAX)) (PreH3 : (retval_2 <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH6 : ((Znth (i + 1 ) (c_string (input)) 0) <= INT_MAX)) (PreH7 : ((Znth i (c_string (input)) 0) <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i >= INT_MIN)) (PreH10 : (left_vowel >= INT_MIN)) (PreH11 : (retval_2 >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH14 : ((Znth (i + 1 ) (c_string (input)) 0) >= INT_MIN)) (PreH15 : ((Znth i (c_string (input)) 0) >= INT_MIN)) (PreH16 : (n >= INT_MIN)) (PreH17 : (retval_2 = 0)) (PreH18 : (retval_2 = 0)) (PreH19 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH20 : (retval = 1)) (PreH21 : (retval = 1)) (PreH22 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH23 : (0 <= ((string_length (input)) + 1 ))) (PreH24 : (i >= 1)) (PreH25 : (n = (string_length (input)))) (PreH26 : (out = 0)) (PreH27 : (3 <= n)) (PreH28 : (n < INT_MAX)) (PreH29 : (0 <= i)) (PreH30 : (i <= (n - 2 ))) (PreH31 : (valid_string input )) (PreH32 : (all_ascii input )) (PreH33 : (problem_118_pre_z input )) (PreH34 : (ascii_range_z input )) (PreH35 : (alpha_codes_z_118 input )) (PreH36 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (c_string (input)) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (c_string (input)) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((Znth (i - 1 ) (c_string (input)) 0) <= 127) ”
.

Definition get_closest_vowel_partial_solve_wit_6_aux := 
forall (word_pre: Z) (input: (@list Z)) (i: Z) (out: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) ))) (PreH4 : (retval = 1)) (PreH5 : (retval = 1)) (PreH6 : (is_vowel_z_118 (Znth i (c_string (input)) 0) )) (PreH7 : (0 <= ((string_length (input)) + 1 ))) (PreH8 : (i >= 1)) (PreH9 : (n = (string_length (input)))) (PreH10 : (out = 0)) (PreH11 : (3 <= n)) (PreH12 : (n < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n - 2 ))) (PreH15 : (valid_string input )) (PreH16 : (all_ascii input )) (PreH17 : (problem_118_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : (alpha_codes_z_118 input )) (PreH20 : (no_candidate_after_z_118 input i )) ,
  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ ((Znth (i - 1 ) (c_string (input)) 0) <= 127) ” 
  &&  “ (0 <= (Znth (i - 1 ) (c_string (input)) 0)) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel_z_118 (Znth (i + 1 ) (c_string (input)) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel_z_118 (Znth i (c_string (input)) 0) ) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_6 := get_closest_vowel_partial_solve_wit_6_pure -> get_closest_vowel_partial_solve_wit_6_aux.

Definition get_closest_vowel_partial_solve_wit_7_pure := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (cur = (Znth (i) (input) (0)))) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (closest_vowel_candidate_z_118 input i )) (PreH14 : (no_candidate_after_z_118 input i )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  (store_string word_pre input )
|--
  “ (2 > 0) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition get_closest_vowel_partial_solve_wit_7_aux := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (cur = (Znth (i) (input) (0)))) (PreH4 : (3 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n - 2 ))) (PreH8 : (valid_string input )) (PreH9 : (all_ascii input )) (PreH10 : (problem_118_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : (alpha_codes_z_118 input )) (PreH13 : (closest_vowel_candidate_z_118 input i )) (PreH14 : (no_candidate_after_z_118 input i )) ,
  (store_string word_pre input )
|--
  “ (2 > 0) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (cur = (Znth (i) (input) (0))) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (closest_vowel_candidate_z_118 input i ) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_7 := get_closest_vowel_partial_solve_wit_7_pure -> get_closest_vowel_partial_solve_wit_7_aux.

Definition get_closest_vowel_partial_solve_wit_8 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_full retval 2 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (cur = (Znth (i) (input) (0))) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (closest_vowel_candidate_z_118 input i ) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 2 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_9 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (cur = (Znth (i) (input) (0)))) (PreH7 : (3 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n - 2 ))) (PreH11 : (valid_string input )) (PreH12 : (all_ascii input )) (PreH13 : (problem_118_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : (alpha_codes_z_118 input )) (PreH16 : (closest_vowel_candidate_z_118 input i )) (PreH17 : (no_candidate_after_z_118 input i )) ,
  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits (cur) (8)))
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (cur = (Znth (i) (input) (0))) ” 
  &&  “ (3 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n - 2 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (closest_vowel_candidate_z_118 input i ) ” 
  &&  “ (no_candidate_after_z_118 input i ) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits (cur) (8)))
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_10_pure := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (i = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : (no_candidate_after_z_118 input 0 )) ,
  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string word_pre input )
|--
  “ (1 > 0) ” 
  &&  “ (1 < INT_MAX) ”
.

Definition get_closest_vowel_partial_solve_wit_10_aux := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (i: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out = 0)) (PreH3 : (i = 0)) (PreH4 : (valid_string input )) (PreH5 : (all_ascii input )) (PreH6 : (problem_118_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (alpha_codes_z_118 input )) (PreH9 : (no_candidate_after_z_118 input 0 )) ,
  (store_string word_pre input )
|--
  “ (1 > 0) ” 
  &&  “ (1 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input 0 ) ”
  &&  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition get_closest_vowel_partial_solve_wit_10 := get_closest_vowel_partial_solve_wit_10_pure -> get_closest_vowel_partial_solve_wit_10_aux.

Definition get_closest_vowel_partial_solve_wit_11 := 
forall (word_pre: Z) (input: (@list Z)) (n: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (out = 0)) (PreH6 : (i = 0)) (PreH7 : (valid_string input )) (PreH8 : (all_ascii input )) (PreH9 : (problem_118_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : (alpha_codes_z_118 input )) (PreH12 : (no_candidate_after_z_118 input 0 )) ,
  (CharArray.undef_full retval 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (all_ascii input ) ” 
  &&  “ (problem_118_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (alpha_codes_z_118 input ) ” 
  &&  “ (no_candidate_after_z_118 input 0 ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 1 )
  **  (CharArray.full word_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_is_vowel_code_118_safety_wit_1 : is_vowel_code_118_safety_wit_1.
Axiom proof_of_is_vowel_code_118_safety_wit_2 : is_vowel_code_118_safety_wit_2.
Axiom proof_of_is_vowel_code_118_safety_wit_3 : is_vowel_code_118_safety_wit_3.
Axiom proof_of_is_vowel_code_118_safety_wit_4 : is_vowel_code_118_safety_wit_4.
Axiom proof_of_is_vowel_code_118_safety_wit_5 : is_vowel_code_118_safety_wit_5.
Axiom proof_of_is_vowel_code_118_safety_wit_6 : is_vowel_code_118_safety_wit_6.
Axiom proof_of_is_vowel_code_118_safety_wit_7 : is_vowel_code_118_safety_wit_7.
Axiom proof_of_is_vowel_code_118_safety_wit_8 : is_vowel_code_118_safety_wit_8.
Axiom proof_of_is_vowel_code_118_safety_wit_9 : is_vowel_code_118_safety_wit_9.
Axiom proof_of_is_vowel_code_118_safety_wit_10 : is_vowel_code_118_safety_wit_10.
Axiom proof_of_is_vowel_code_118_safety_wit_11 : is_vowel_code_118_safety_wit_11.
Axiom proof_of_is_vowel_code_118_safety_wit_12 : is_vowel_code_118_safety_wit_12.
Axiom proof_of_is_vowel_code_118_safety_wit_13 : is_vowel_code_118_safety_wit_13.
Axiom proof_of_is_vowel_code_118_safety_wit_14 : is_vowel_code_118_safety_wit_14.
Axiom proof_of_is_vowel_code_118_safety_wit_15 : is_vowel_code_118_safety_wit_15.
Axiom proof_of_is_vowel_code_118_safety_wit_16 : is_vowel_code_118_safety_wit_16.
Axiom proof_of_is_vowel_code_118_safety_wit_17 : is_vowel_code_118_safety_wit_17.
Axiom proof_of_is_vowel_code_118_safety_wit_18 : is_vowel_code_118_safety_wit_18.
Axiom proof_of_is_vowel_code_118_safety_wit_19 : is_vowel_code_118_safety_wit_19.
Axiom proof_of_is_vowel_code_118_safety_wit_20 : is_vowel_code_118_safety_wit_20.
Axiom proof_of_is_vowel_code_118_safety_wit_21 : is_vowel_code_118_safety_wit_21.
Axiom proof_of_is_vowel_code_118_return_wit_1 : is_vowel_code_118_return_wit_1.
Axiom proof_of_is_vowel_code_118_return_wit_2 : is_vowel_code_118_return_wit_2.
Axiom proof_of_is_vowel_code_118_return_wit_3 : is_vowel_code_118_return_wit_3.
Axiom proof_of_is_vowel_code_118_return_wit_4 : is_vowel_code_118_return_wit_4.
Axiom proof_of_is_vowel_code_118_return_wit_5 : is_vowel_code_118_return_wit_5.
Axiom proof_of_is_vowel_code_118_return_wit_6 : is_vowel_code_118_return_wit_6.
Axiom proof_of_is_vowel_code_118_return_wit_7 : is_vowel_code_118_return_wit_7.
Axiom proof_of_is_vowel_code_118_return_wit_8 : is_vowel_code_118_return_wit_8.
Axiom proof_of_is_vowel_code_118_return_wit_9 : is_vowel_code_118_return_wit_9.
Axiom proof_of_is_vowel_code_118_return_wit_10 : is_vowel_code_118_return_wit_10.
Axiom proof_of_is_vowel_code_118_return_wit_11 : is_vowel_code_118_return_wit_11.
Axiom proof_of_get_closest_vowel_safety_wit_1 : get_closest_vowel_safety_wit_1.
Axiom proof_of_get_closest_vowel_safety_wit_2 : get_closest_vowel_safety_wit_2.
Axiom proof_of_get_closest_vowel_safety_wit_3 : get_closest_vowel_safety_wit_3.
Axiom proof_of_get_closest_vowel_safety_wit_4 : get_closest_vowel_safety_wit_4.
Axiom proof_of_get_closest_vowel_safety_wit_5 : get_closest_vowel_safety_wit_5.
Axiom proof_of_get_closest_vowel_safety_wit_6 : get_closest_vowel_safety_wit_6.
Axiom proof_of_get_closest_vowel_safety_wit_7 : get_closest_vowel_safety_wit_7.
Axiom proof_of_get_closest_vowel_safety_wit_8 : get_closest_vowel_safety_wit_8.
Axiom proof_of_get_closest_vowel_safety_wit_9 : get_closest_vowel_safety_wit_9.
Axiom proof_of_get_closest_vowel_safety_wit_10 : get_closest_vowel_safety_wit_10.
Axiom proof_of_get_closest_vowel_safety_wit_11 : get_closest_vowel_safety_wit_11.
Axiom proof_of_get_closest_vowel_safety_wit_12 : get_closest_vowel_safety_wit_12.
Axiom proof_of_get_closest_vowel_safety_wit_13 : get_closest_vowel_safety_wit_13.
Axiom proof_of_get_closest_vowel_safety_wit_14 : get_closest_vowel_safety_wit_14.
Axiom proof_of_get_closest_vowel_safety_wit_15 : get_closest_vowel_safety_wit_15.
Axiom proof_of_get_closest_vowel_safety_wit_16 : get_closest_vowel_safety_wit_16.
Axiom proof_of_get_closest_vowel_safety_wit_17 : get_closest_vowel_safety_wit_17.
Axiom proof_of_get_closest_vowel_safety_wit_18 : get_closest_vowel_safety_wit_18.
Axiom proof_of_get_closest_vowel_safety_wit_19 : get_closest_vowel_safety_wit_19.
Axiom proof_of_get_closest_vowel_safety_wit_20 : get_closest_vowel_safety_wit_20.
Axiom proof_of_get_closest_vowel_safety_wit_21 : get_closest_vowel_safety_wit_21.
Axiom proof_of_get_closest_vowel_safety_wit_22 : get_closest_vowel_safety_wit_22.
Axiom proof_of_get_closest_vowel_safety_wit_23 : get_closest_vowel_safety_wit_23.
Axiom proof_of_get_closest_vowel_safety_wit_24 : get_closest_vowel_safety_wit_24.
Axiom proof_of_get_closest_vowel_safety_wit_25 : get_closest_vowel_safety_wit_25.
Axiom proof_of_get_closest_vowel_safety_wit_26 : get_closest_vowel_safety_wit_26.
Axiom proof_of_get_closest_vowel_safety_wit_27 : get_closest_vowel_safety_wit_27.
Axiom proof_of_get_closest_vowel_safety_wit_28 : get_closest_vowel_safety_wit_28.
Axiom proof_of_get_closest_vowel_safety_wit_29 : get_closest_vowel_safety_wit_29.
Axiom proof_of_get_closest_vowel_safety_wit_30 : get_closest_vowel_safety_wit_30.
Axiom proof_of_get_closest_vowel_safety_wit_31 : get_closest_vowel_safety_wit_31.
Axiom proof_of_get_closest_vowel_safety_wit_32 : get_closest_vowel_safety_wit_32.
Axiom proof_of_get_closest_vowel_safety_wit_33 : get_closest_vowel_safety_wit_33.
Axiom proof_of_get_closest_vowel_safety_wit_34 : get_closest_vowel_safety_wit_34.
Axiom proof_of_get_closest_vowel_safety_wit_35 : get_closest_vowel_safety_wit_35.
Axiom proof_of_get_closest_vowel_safety_wit_36 : get_closest_vowel_safety_wit_36.
Axiom proof_of_get_closest_vowel_safety_wit_37 : get_closest_vowel_safety_wit_37.
Axiom proof_of_get_closest_vowel_safety_wit_38 : get_closest_vowel_safety_wit_38.
Axiom proof_of_get_closest_vowel_safety_wit_39 : get_closest_vowel_safety_wit_39.
Axiom proof_of_get_closest_vowel_safety_wit_40 : get_closest_vowel_safety_wit_40.
Axiom proof_of_get_closest_vowel_safety_wit_41 : get_closest_vowel_safety_wit_41.
Axiom proof_of_get_closest_vowel_safety_wit_42 : get_closest_vowel_safety_wit_42.
Axiom proof_of_get_closest_vowel_safety_wit_43 : get_closest_vowel_safety_wit_43.
Axiom proof_of_get_closest_vowel_safety_wit_44 : get_closest_vowel_safety_wit_44.
Axiom proof_of_get_closest_vowel_safety_wit_45 : get_closest_vowel_safety_wit_45.
Axiom proof_of_get_closest_vowel_entail_wit_1 : get_closest_vowel_entail_wit_1.
Axiom proof_of_get_closest_vowel_entail_wit_2 : get_closest_vowel_entail_wit_2.
Axiom proof_of_get_closest_vowel_entail_wit_3 : get_closest_vowel_entail_wit_3.
Axiom proof_of_get_closest_vowel_entail_wit_4_1 : get_closest_vowel_entail_wit_4_1.
Axiom proof_of_get_closest_vowel_entail_wit_4_2 : get_closest_vowel_entail_wit_4_2.
Axiom proof_of_get_closest_vowel_entail_wit_4_3 : get_closest_vowel_entail_wit_4_3.
Axiom proof_of_get_closest_vowel_entail_wit_5 : get_closest_vowel_entail_wit_5.
Axiom proof_of_get_closest_vowel_entail_wit_6 : get_closest_vowel_entail_wit_6.
Axiom proof_of_get_closest_vowel_return_wit_1 : get_closest_vowel_return_wit_1.
Axiom proof_of_get_closest_vowel_return_wit_2 : get_closest_vowel_return_wit_2.
Axiom proof_of_get_closest_vowel_return_wit_3 : get_closest_vowel_return_wit_3.
Axiom proof_of_get_closest_vowel_partial_solve_wit_1_pure : get_closest_vowel_partial_solve_wit_1_pure.
Axiom proof_of_get_closest_vowel_partial_solve_wit_1 : get_closest_vowel_partial_solve_wit_1.
Axiom proof_of_get_closest_vowel_partial_solve_wit_2_pure : get_closest_vowel_partial_solve_wit_2_pure.
Axiom proof_of_get_closest_vowel_partial_solve_wit_2 : get_closest_vowel_partial_solve_wit_2.
Axiom proof_of_get_closest_vowel_partial_solve_wit_3 : get_closest_vowel_partial_solve_wit_3.
Axiom proof_of_get_closest_vowel_partial_solve_wit_4_pure : get_closest_vowel_partial_solve_wit_4_pure.
Axiom proof_of_get_closest_vowel_partial_solve_wit_4 : get_closest_vowel_partial_solve_wit_4.
Axiom proof_of_get_closest_vowel_partial_solve_wit_5_pure : get_closest_vowel_partial_solve_wit_5_pure.
Axiom proof_of_get_closest_vowel_partial_solve_wit_5 : get_closest_vowel_partial_solve_wit_5.
Axiom proof_of_get_closest_vowel_partial_solve_wit_6_pure : get_closest_vowel_partial_solve_wit_6_pure.
Axiom proof_of_get_closest_vowel_partial_solve_wit_6 : get_closest_vowel_partial_solve_wit_6.
Axiom proof_of_get_closest_vowel_partial_solve_wit_7_pure : get_closest_vowel_partial_solve_wit_7_pure.
Axiom proof_of_get_closest_vowel_partial_solve_wit_7 : get_closest_vowel_partial_solve_wit_7.
Axiom proof_of_get_closest_vowel_partial_solve_wit_8 : get_closest_vowel_partial_solve_wit_8.
Axiom proof_of_get_closest_vowel_partial_solve_wit_9 : get_closest_vowel_partial_solve_wit_9.
Axiom proof_of_get_closest_vowel_partial_solve_wit_10_pure : get_closest_vowel_partial_solve_wit_10_pure.
Axiom proof_of_get_closest_vowel_partial_solve_wit_10 : get_closest_vowel_partial_solve_wit_10.
Axiom proof_of_get_closest_vowel_partial_solve_wit_11 : get_closest_vowel_partial_solve_wit_11.

End VC_Correct.
