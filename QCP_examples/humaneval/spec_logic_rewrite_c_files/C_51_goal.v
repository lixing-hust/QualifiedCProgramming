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
Require Import coins_51.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function remove_vowels -----*)

Definition remove_vowels_safety_wit_1 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (PreH1 : (text_pre = text0)) (PreH2 : (valid_string input_l )) (PreH3 : (problem_51_pre_z input_l )) (PreH4 : (vowel_payload_safe_51 )) (PreH5 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_stringLit (LitMap (("AEIOUaeiou"%string))) ("AEIOUaeiou"%string) )
  **  (GlobalStrings_missing LitMap (cons (("AEIOUaeiou"%string)) ((@nil string))) )
  **  ((( &( "vowels" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition remove_vowels_safety_wit_2 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (PreH1 : (text_pre = text0)) (PreH2 : (valid_string input_l )) (PreH3 : (problem_51_pre_z input_l )) (PreH4 : (vowel_payload_safe_51 )) (PreH5 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_stringLit (LitMap (("AEIOUaeiou"%string))) ("AEIOUaeiou"%string) )
  **  (GlobalStrings_missing LitMap (cons (("AEIOUaeiou"%string)) ((@nil string))) )
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition remove_vowels_safety_wit_3 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (text_pre = text0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_51_pre_z input_l )) (PreH6 : (vowel_payload_safe_51 )) (PreH7 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string text_pre input_l )
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition remove_vowels_safety_wit_4 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (text_pre = text0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_51_pre_z input_l )) (PreH6 : (vowel_payload_safe_51 )) (PreH7 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string text_pre input_l )
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition remove_vowels_safety_wit_5 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input_l)))) (PreH3 : (0 <= ((string_length (input_l)) + 1 ))) (PreH4 : (text_pre = text0)) (PreH5 : (valid_string input_l )) (PreH6 : (problem_51_pre_z input_l )) (PreH7 : (vowel_payload_safe_51 )) (PreH8 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition remove_vowels_safety_wit_6 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ False ”
.

Definition remove_vowels_safety_wit_7 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition remove_vowels_safety_wit_8 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH2 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH3 : (0 <= ((string_length (input_l)) + 1 ))) (PreH4 : (i < n)) (PreH5 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (j = (Zlength (output_l)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= j)) (PreH11 : (j <= i)) (PreH12 : (valid_string input_l )) (PreH13 : (problem_51_pre_z input_l )) (PreH14 : (vowel_payload_safe_51 )) (PreH15 : (filter_prefix_51 input_l i output_l )) (PreH16 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string vowels vowel_payload_51 )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition remove_vowels_safety_wit_9 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full out (j + 1 ) (app (output_l) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (j + 1 ) (n + 1 ) )
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition remove_vowels_safety_wit_10 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full out (j + 1 ) (app (output_l) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (j + 1 ) (n + 1 ) )
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition remove_vowels_safety_wit_11 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full out (j + 1 ) (app (output_l) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (j + 1 ) (n + 1 ) )
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition remove_vowels_safety_wit_12 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string vowels vowel_payload_51 )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition remove_vowels_safety_wit_13 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i >= n)) (PreH2 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (j = (Zlength (output_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_51_pre_z input_l )) (PreH11 : (vowel_payload_safe_51 )) (PreH12 : (filter_prefix_51 input_l i output_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string text0 input_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (store_string vowels vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition remove_vowels_entail_wit_1 := 
(
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  EX (output_l: (@list Z)) ,
  “ (((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ) = (vowel_ptr_51 (LitMap))) ” 
  &&  “ (retval = (string_length (input_l))) ” 
  &&  “ (0 = (Zlength (output_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (filter_prefix_51 input_l 0 output_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  ((( &( "text" ) )) # Ptr  |-> text0)
  **  (store_string text0 input_l )
  **  (CharArray.full retval_2 0 output_l )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
  **  (store_string ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ) vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
) \/
(
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
|--
  “ (filter_prefix_51 input_l 0 (@nil Z) ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ) = (vowel_ptr_51 (LitMap))) ”
  &&  (CharArray.full ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ) ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
).

Definition remove_vowels_entail_wit_1_split_goal_1 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
|--
  “ (filter_prefix_51 input_l 0 (@nil Z) ) ”
.

Definition remove_vowels_entail_wit_1_split_goal_2 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= retval) ”
.

Definition remove_vowels_entail_wit_1_split_goal_3 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition remove_vowels_entail_wit_1_split_goal_4 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
|--
  “ (((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ) = (vowel_ptr_51 (LitMap))) ”
.

Definition remove_vowels_entail_wit_1_split_goal_spatial := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input_l)))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (text_pre = text0)) (PreH6 : (valid_string input_l )) (PreH7 : (problem_51_pre_z input_l )) (PreH8 : (vowel_payload_safe_51 )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
|--
  (CharArray.full ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ) ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
.

Definition remove_vowels_entail_wit_2_1 := 
(
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full out (j + 1 ) (app (output_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (j + 1 ) (n + 1 ) )
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  EX (output_l: (@list Z)) ,
  “ (vowels = (vowel_ptr_51 (LitMap))) ” 
  &&  “ (n = (string_length (input_l))) ” 
  &&  “ ((j + 1 ) = (Zlength (output_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (i + 1 )) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (filter_prefix_51 input_l (i + 1 ) output_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (store_string text0 input_l )
  **  (CharArray.full out (j + 1 ) output_l )
  **  (CharArray.undef_seg out (j + 1 ) (n + 1 ) )
  **  (store_string vowels vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
) \/
(
forall (input_l: (@list Z)) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (filter_prefix_51 input_l (i + 1 ) (app (output_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z))))) ) ” 
  &&  “ ((j + 1 ) = (Zlength ((app (output_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z)))))))) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_51 )
).

Definition remove_vowels_entail_wit_2_1_split_goal_1 := 
forall (input_l: (@list Z)) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (filter_prefix_51 input_l (i + 1 ) (app (output_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z))))) ) ”
.

Definition remove_vowels_entail_wit_2_1_split_goal_2 := 
forall (input_l: (@list Z)) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((j + 1 ) = (Zlength ((app (output_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (input_l)) 0)) (8))) ((@nil Z)))))))) ”
.

Definition remove_vowels_entail_wit_2_1_split_goal_spatial := 
forall (input_l: (@list Z)) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
.

Definition remove_vowels_entail_wit_2_2 := 
(
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string vowels vowel_payload_51 )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (CharArray.full out j output_l_2 )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  EX (output_l: (@list Z)) ,
  “ (vowels = (vowel_ptr_51 (LitMap))) ” 
  &&  “ (n = (string_length (input_l))) ” 
  &&  “ (j = (Zlength (output_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (filter_prefix_51 input_l (i + 1 ) output_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (store_string text0 input_l )
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (store_string vowels vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
) \/
(
forall (input_l: (@list Z)) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (filter_prefix_51 input_l (i + 1 ) output_l_2 ) ”
  &&  (GlobalStrings_missing LitMap all_vowel_literals_51 )
).

Definition remove_vowels_entail_wit_2_2_split_goal_1 := 
forall (input_l: (@list Z)) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (filter_prefix_51 input_l (i + 1 ) output_l_2 ) ”
.

Definition remove_vowels_entail_wit_2_2_split_goal_spatial := 
forall (input_l: (@list Z)) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l_2)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l_2 )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  (GlobalStrings_missing LitMap all_vowel_literals_51 )
.

Definition remove_vowels_return_wit_1 := 
(
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (j = (Zlength (output_l_2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_51_pre_z input_l )) (PreH13 : (vowel_payload_safe_51 )) (PreH14 : (filter_prefix_51 input_l i output_l_2 )) (PreH15 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full out (j + 1 ) (app (output_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (j + 1 ) (n + 1 ) )
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  EX (output_l: (@list Z)) ,
  “ (problem_51_spec_z input_l output_l ) ” 
  &&  “ ((Zlength (output_l)) <= (string_length (input_l))) ”
  &&  (store_string text0 input_l )
  **  (store_string out output_l )
  **  (CharArray.undef_seg out ((Zlength (output_l)) + 1 ) ((string_length (input_l)) + 1 ) )
  **  (store_string (vowel_ptr_51 (LitMap)) vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
) \/
(
forall (input_l: (@list Z)) (out: Z) (i: Z) (output_l_2: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (0 <= (j + 1 ))) (PreH2 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH3 : (0 <= ((string_length (input_l)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (j = (Zlength (output_l_2)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= j)) (PreH11 : (j <= i)) (PreH12 : (valid_string input_l )) (PreH13 : (problem_51_pre_z input_l )) (PreH14 : (vowel_payload_safe_51 )) (PreH15 : (filter_prefix_51 input_l i output_l_2 )) (PreH16 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full out (j + 1 ) (app (output_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (j + 1 ) (n + 1 ) )
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  EX (output_l: (@list Z)) ,
  “ (problem_51_spec_z input_l output_l ) ” 
  &&  “ ((Zlength (output_l)) <= (string_length (input_l))) ”
  &&  (CharArray.full (vowel_ptr_51 (LitMap)) ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full out ((string_length (output_l)) + 1 ) (c_string (output_l)) )
  **  (CharArray.undef_seg out ((Zlength (output_l)) + 1 ) ((string_length (input_l)) + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
).

Definition remove_vowels_partial_solve_wit_1_pure := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (PreH1 : (text_pre = text0)) (PreH2 : (valid_string input_l )) (PreH3 : (problem_51_pre_z input_l )) (PreH4 : (vowel_payload_safe_51 )) (PreH5 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_stringLit (LitMap (("AEIOUaeiou"%string))) ("AEIOUaeiou"%string) )
  **  (GlobalStrings_missing LitMap (cons (("AEIOUaeiou"%string)) ((@nil string))) )
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_l )
|--
  “ (valid_string input_l ) ” 
  &&  “ ((string_length (input_l)) < INT_MAX) ”
.

Definition remove_vowels_partial_solve_wit_1_aux := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (PreH1 : (text_pre = text0)) (PreH2 : (valid_string input_l )) (PreH3 : (problem_51_pre_z input_l )) (PreH4 : (vowel_payload_safe_51 )) (PreH5 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_stringLit (LitMap (("AEIOUaeiou"%string))) ("AEIOUaeiou"%string) )
  **  (GlobalStrings_missing LitMap (cons (("AEIOUaeiou"%string)) ((@nil string))) )
  **  (store_string text_pre input_l )
|--
  “ (valid_string input_l ) ” 
  &&  “ ((string_length (input_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input_l)) + 1 )) ” 
  &&  “ (text_pre = text0) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (store_string text_pre input_l )
  **  (GlobalStrings LitMap )
.

Definition remove_vowels_partial_solve_wit_1 := remove_vowels_partial_solve_wit_1_pure -> remove_vowels_partial_solve_wit_1_aux.

Definition remove_vowels_partial_solve_wit_2_pure := 
(
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (text_pre = text0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_51_pre_z input_l )) (PreH6 : (vowel_payload_safe_51 )) (PreH7 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string text_pre input_l )
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ”
) \/
(
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (string_length (input_l)))) (PreH6 : (0 <= ((string_length (input_l)) + 1 ))) (PreH7 : (text_pre = text0)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_51_pre_z input_l )) (PreH10 : (vowel_payload_safe_51 )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 < (retval + 1 )) ”
).

Definition remove_vowels_partial_solve_wit_2_pure_split_goal_1 := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (string_length (input_l)))) (PreH6 : (0 <= ((string_length (input_l)) + 1 ))) (PreH7 : (text_pre = text0)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_51_pre_z input_l )) (PreH10 : (vowel_payload_safe_51 )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "vowels" ) )) # Ptr  |-> ((LitMap (("AEIOUaeiou"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 < (retval + 1 )) ”
.

Definition remove_vowels_partial_solve_wit_2_aux := 
forall (text_pre: Z) (text0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (text_pre = text0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_51_pre_z input_l )) (PreH6 : (vowel_payload_safe_51 )) (PreH7 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string text_pre input_l )
  **  (GlobalStrings LitMap )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ” 
  &&  “ (retval = (string_length (input_l))) ” 
  &&  “ (0 <= ((string_length (input_l)) + 1 )) ” 
  &&  “ (text_pre = text0) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.full text_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (GlobalStrings LitMap )
.

Definition remove_vowels_partial_solve_wit_2 := remove_vowels_partial_solve_wit_2_pure -> remove_vowels_partial_solve_wit_2_aux.

Definition remove_vowels_partial_solve_wit_3_pure := 
(
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i < n)) (PreH2 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (j = (Zlength (output_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_51_pre_z input_l )) (PreH11 : (vowel_payload_safe_51 )) (PreH12 : (filter_prefix_51 input_l i output_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string text0 input_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (store_string vowels vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((string_length (vowel_payload_51)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (input_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (input_l)) 0)) ” 
  &&  “ (valid_string vowel_payload_51 ) ”
) \/
(
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (input_l)) 0) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (input_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH10 : (0 <= ((string_length (input_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH13 : (n = (string_length (input_l)))) (PreH14 : (j = (Zlength (output_l)))) (PreH15 : (0 <= i)) (PreH16 : (i <= n)) (PreH17 : (0 <= j)) (PreH18 : (j <= i)) (PreH19 : (valid_string input_l )) (PreH20 : (problem_51_pre_z input_l )) (PreH21 : (vowel_payload_safe_51 )) (PreH22 : (filter_prefix_51 input_l i output_l )) (PreH23 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (valid_string vowel_payload_51 ) ” 
  &&  “ (0 <= (Znth i (c_string (input_l)) 0)) ” 
  &&  “ ((Znth i (c_string (input_l)) 0) <= 127) ” 
  &&  “ ((string_length (vowel_payload_51)) < INT_MAX) ”
).

Definition remove_vowels_partial_solve_wit_3_pure_split_goal_1 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (input_l)) 0) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (input_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH10 : (0 <= ((string_length (input_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH13 : (n = (string_length (input_l)))) (PreH14 : (j = (Zlength (output_l)))) (PreH15 : (0 <= i)) (PreH16 : (i <= n)) (PreH17 : (0 <= j)) (PreH18 : (j <= i)) (PreH19 : (valid_string input_l )) (PreH20 : (problem_51_pre_z input_l )) (PreH21 : (vowel_payload_safe_51 )) (PreH22 : (filter_prefix_51 input_l i output_l )) (PreH23 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (valid_string vowel_payload_51 ) ”
.

Definition remove_vowels_partial_solve_wit_3_pure_split_goal_2 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (input_l)) 0) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (input_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH10 : (0 <= ((string_length (input_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH13 : (n = (string_length (input_l)))) (PreH14 : (j = (Zlength (output_l)))) (PreH15 : (0 <= i)) (PreH16 : (i <= n)) (PreH17 : (0 <= j)) (PreH18 : (j <= i)) (PreH19 : (valid_string input_l )) (PreH20 : (problem_51_pre_z input_l )) (PreH21 : (vowel_payload_safe_51 )) (PreH22 : (filter_prefix_51 input_l i output_l )) (PreH23 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (0 <= (Znth i (c_string (input_l)) 0)) ”
.

Definition remove_vowels_partial_solve_wit_3_pure_split_goal_3 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (input_l)) 0) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (input_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH10 : (0 <= ((string_length (input_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH13 : (n = (string_length (input_l)))) (PreH14 : (j = (Zlength (output_l)))) (PreH15 : (0 <= i)) (PreH16 : (i <= n)) (PreH17 : (0 <= j)) (PreH18 : (j <= i)) (PreH19 : (valid_string input_l )) (PreH20 : (problem_51_pre_z input_l )) (PreH21 : (vowel_payload_safe_51 )) (PreH22 : (filter_prefix_51 input_l i output_l )) (PreH23 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((Znth i (c_string (input_l)) 0) <= 127) ”
.

Definition remove_vowels_partial_solve_wit_3_pure_split_goal_4 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (j <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((Znth i (c_string (input_l)) 0) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (n >= INT_MIN)) (PreH8 : ((Znth i (c_string (input_l)) 0) >= INT_MIN)) (PreH9 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH10 : (0 <= ((string_length (input_l)) + 1 ))) (PreH11 : (i < n)) (PreH12 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH13 : (n = (string_length (input_l)))) (PreH14 : (j = (Zlength (output_l)))) (PreH15 : (0 <= i)) (PreH16 : (i <= n)) (PreH17 : (0 <= j)) (PreH18 : (j <= i)) (PreH19 : (valid_string input_l )) (PreH20 : (problem_51_pre_z input_l )) (PreH21 : (vowel_payload_safe_51 )) (PreH22 : (filter_prefix_51 input_l i output_l )) (PreH23 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  ((( &( "found" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text0)
  **  ((( &( "vowels" ) )) # Ptr  |-> vowels)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((string_length (vowel_payload_51)) < INT_MAX) ”
.

Definition remove_vowels_partial_solve_wit_3_aux := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i < n)) (PreH2 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (j = (Zlength (output_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_51_pre_z input_l )) (PreH11 : (vowel_payload_safe_51 )) (PreH12 : (filter_prefix_51 input_l i output_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string text0 input_l )
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (store_string vowels vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ ((string_length (vowel_payload_51)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (input_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (input_l)) 0)) ” 
  &&  “ (valid_string vowel_payload_51 ) ” 
  &&  “ (0 <= ((string_length (vowel_payload_51)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input_l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (vowels = (vowel_ptr_51 (LitMap))) ” 
  &&  “ (n = (string_length (input_l))) ” 
  &&  “ (j = (Zlength (output_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (filter_prefix_51 input_l i output_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (store_string vowels vowel_payload_51 )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
.

Definition remove_vowels_partial_solve_wit_3 := remove_vowels_partial_solve_wit_3_pure -> remove_vowels_partial_solve_wit_3_aux.

Definition remove_vowels_partial_solve_wit_4 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels )) (PreH3 : (0 <= ((string_length (vowel_payload_51)) + 1 ))) (PreH4 : (0 <= ((string_length (input_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH7 : (n = (string_length (input_l)))) (PreH8 : (j = (Zlength (output_l)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (valid_string input_l )) (PreH14 : (problem_51_pre_z input_l )) (PreH15 : (vowel_payload_safe_51 )) (PreH16 : (filter_prefix_51 input_l i output_l )) (PreH17 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string vowels vowel_payload_51 )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (retval = 0) ” 
  &&  “ (strchr_result vowel_payload_51 (Znth i (c_string (input_l)) 0) retval vowels ) ” 
  &&  “ (0 <= ((string_length (vowel_payload_51)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input_l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (vowels = (vowel_ptr_51 (LitMap))) ” 
  &&  “ (n = (string_length (input_l))) ” 
  &&  “ (j = (Zlength (output_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (filter_prefix_51 input_l i output_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (((out + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.undef_missing_i out j j (n + 1 ) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (CharArray.full out j output_l )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
.

Definition remove_vowels_partial_solve_wit_5 := 
forall (text0: Z) (input_l: (@list Z)) (out: Z) (i: Z) (output_l: (@list Z)) (j: Z) (n: Z) (vowels: Z) (PreH1 : (i >= n)) (PreH2 : (vowels = (vowel_ptr_51 (LitMap)))) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (j = (Zlength (output_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_51_pre_z input_l )) (PreH11 : (vowel_payload_safe_51 )) (PreH12 : (filter_prefix_51 input_l i output_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string text0 input_l )
  **  (CharArray.full out j output_l )
  **  (CharArray.undef_seg out j (n + 1 ) )
  **  (store_string vowels vowel_payload_51 )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
|--
  “ (0 <= ((string_length (vowel_payload_51)) + 1 )) ” 
  &&  “ (0 <= ((string_length (input_l)) + 1 )) ” 
  &&  “ (i >= n) ” 
  &&  “ (vowels = (vowel_ptr_51 (LitMap))) ” 
  &&  “ (n = (string_length (input_l))) ” 
  &&  “ (j = (Zlength (output_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_51_pre_z input_l ) ” 
  &&  “ (vowel_payload_safe_51 ) ” 
  &&  “ (filter_prefix_51 input_l i output_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (((out + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full vowels ((string_length (vowel_payload_51)) + 1 ) (c_string (vowel_payload_51)) )
  **  (CharArray.full text0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
  **  (CharArray.undef_missing_i out j j (n + 1 ) )
  **  (CharArray.full out j output_l )
  **  (GlobalStrings_missing LitMap all_vowel_literals_51 )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_remove_vowels_safety_wit_1 : remove_vowels_safety_wit_1.
Axiom proof_of_remove_vowels_safety_wit_2 : remove_vowels_safety_wit_2.
Axiom proof_of_remove_vowels_safety_wit_3 : remove_vowels_safety_wit_3.
Axiom proof_of_remove_vowels_safety_wit_4 : remove_vowels_safety_wit_4.
Axiom proof_of_remove_vowels_safety_wit_5 : remove_vowels_safety_wit_5.
Axiom proof_of_remove_vowels_safety_wit_6 : remove_vowels_safety_wit_6.
Axiom proof_of_remove_vowels_safety_wit_7 : remove_vowels_safety_wit_7.
Axiom proof_of_remove_vowels_safety_wit_8 : remove_vowels_safety_wit_8.
Axiom proof_of_remove_vowels_safety_wit_9 : remove_vowels_safety_wit_9.
Axiom proof_of_remove_vowels_safety_wit_10 : remove_vowels_safety_wit_10.
Axiom proof_of_remove_vowels_safety_wit_11 : remove_vowels_safety_wit_11.
Axiom proof_of_remove_vowels_safety_wit_12 : remove_vowels_safety_wit_12.
Axiom proof_of_remove_vowels_safety_wit_13 : remove_vowels_safety_wit_13.
Axiom proof_of_remove_vowels_entail_wit_1 : remove_vowels_entail_wit_1.
Axiom proof_of_remove_vowels_entail_wit_2_1 : remove_vowels_entail_wit_2_1.
Axiom proof_of_remove_vowels_entail_wit_2_2 : remove_vowels_entail_wit_2_2.
Axiom proof_of_remove_vowels_return_wit_1 : remove_vowels_return_wit_1.
Axiom proof_of_remove_vowels_partial_solve_wit_1_pure : remove_vowels_partial_solve_wit_1_pure.
Axiom proof_of_remove_vowels_partial_solve_wit_1 : remove_vowels_partial_solve_wit_1.
Axiom proof_of_remove_vowels_partial_solve_wit_2_pure : remove_vowels_partial_solve_wit_2_pure.
Axiom proof_of_remove_vowels_partial_solve_wit_2 : remove_vowels_partial_solve_wit_2.
Axiom proof_of_remove_vowels_partial_solve_wit_3_pure : remove_vowels_partial_solve_wit_3_pure.
Axiom proof_of_remove_vowels_partial_solve_wit_3 : remove_vowels_partial_solve_wit_3.
Axiom proof_of_remove_vowels_partial_solve_wit_4 : remove_vowels_partial_solve_wit_4.
Axiom proof_of_remove_vowels_partial_solve_wit_5 : remove_vowels_partial_solve_wit_5.

End VC_Correct.
