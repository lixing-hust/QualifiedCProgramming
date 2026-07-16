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
Require Import coins_89.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function encrypt -----*)

Definition encrypt_safety_wit_1 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition encrypt_safety_wit_2 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition encrypt_safety_wit_3 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (valid_string input )) (PreH5 : (problem_89_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition encrypt_safety_wit_4 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ False ”
.

Definition encrypt_safety_wit_5 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition encrypt_safety_wit_6 := 
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 )) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 )) ”
).

Definition encrypt_safety_wit_6_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ”
.

Definition encrypt_safety_wit_6_split_goal_2 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= (((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 )) ”
.

Definition encrypt_safety_wit_7 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((((Znth i (c_string (input)) 0) + 4 ) - 97 ) <> (INT_MIN)) \/ (26 <> (-1))) ” 
  &&  “ (26 <> 0) ”
.

Definition encrypt_safety_wit_8 := 
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (input)) 0) + 4 ) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i (c_string (input)) 0) + 4 ) - 97 )) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (input)) 0) + 4 ) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i (c_string (input)) 0) + 4 ) - 97 )) ”
).

Definition encrypt_safety_wit_8_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (input)) 0) + 4 ) - 97 ) <= INT_MAX) ”
.

Definition encrypt_safety_wit_8_split_goal_2 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= (((Znth i (c_string (input)) 0) + 4 ) - 97 )) ”
.

Definition encrypt_safety_wit_9 := 
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (input)) 0) + 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (input)) 0) + 4 )) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (input)) 0) + 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (input)) 0) + 4 )) ”
).

Definition encrypt_safety_wit_9_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (input)) 0) + 4 ) <= INT_MAX) ”
.

Definition encrypt_safety_wit_9_split_goal_2 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (input)) 0) + 4 )) ”
.

Definition encrypt_safety_wit_10 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition encrypt_safety_wit_11 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition encrypt_safety_wit_12 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (26 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 26) ”
.

Definition encrypt_safety_wit_13 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition encrypt_safety_wit_14 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_89_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : (lowercase_codes_z_89 input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (rotate_prefix_z_89 input output i )) ,
  (CharArray.full out (i + 1 ) (app (output) ((cons ((signed_last_nbits ((((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition encrypt_safety_wit_15 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition encrypt_entail_wit_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (retval = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_89_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (lowercase_codes_z_89 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (rotate_prefix_z_89 input output 0 ) ”
  &&  (store_string s_pre input )
  **  (CharArray.full retval_2 0 output )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
) \/
(
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (rotate_prefix_z_89 input (@nil Z) 0 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (lowercase_codes_z_89 input ) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
).

Definition encrypt_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (rotate_prefix_z_89 input (@nil Z) 0 ) ”
.

Definition encrypt_entail_wit_1_split_goal_2 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (0 <= retval) ”
.

Definition encrypt_entail_wit_1_split_goal_3 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (lowercase_codes_z_89 input ) ”
.

Definition encrypt_entail_wit_1_split_goal_spatial := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  (CharArray.undef_full retval_2 (retval + 1 ) )
.

Definition encrypt_entail_wit_2 := 
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_89_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : (lowercase_codes_z_89 input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (rotate_prefix_z_89 input output_2 i )) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_89_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (lowercase_codes_z_89 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (rotate_prefix_z_89 input output (i + 1 ) ) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_89_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : (lowercase_codes_z_89 input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (rotate_prefix_z_89 input output_2 i )) ,
  TT && emp 
|--
  “ (rotate_prefix_z_89 input (app (output_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition encrypt_entail_wit_2_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_89_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : (lowercase_codes_z_89 input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (rotate_prefix_z_89 input output_2 i )) ,
  TT && emp 
|--
  “ (rotate_prefix_z_89 input (app (output_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (input)) 0) + 4 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) (i + 1 ) ) ”
.

Definition encrypt_return_wit_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_89_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : (lowercase_codes_z_89 input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (rotate_prefix_z_89 input output_2 i )) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (n + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_89_spec_z input output ) ”
  &&  (store_string s_pre input )
  **  (store_string out output )
) \/
(
forall (input: (@list Z)) (out: Z) (output_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : (lowercase_codes_z_89 input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (rotate_prefix_z_89 input output_2 i )) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons (0) ((@nil Z))))) )
|--
  EX (output: (@list Z)) ,
  “ (problem_89_spec_z input output ) ”
  &&  (CharArray.full out ((string_length (output)) + 1 ) (c_string (output)) )
).

Definition encrypt_partial_solve_wit_1_pure := 
forall (s_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_89_pre_z input )) (PreH3 : (ascii_range_z input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition encrypt_partial_solve_wit_1_aux := 
forall (s_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_89_pre_z input )) (PreH3 : (ascii_range_z input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_89_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
.

Definition encrypt_partial_solve_wit_1 := encrypt_partial_solve_wit_1_pure -> encrypt_partial_solve_wit_1_aux.

Definition encrypt_partial_solve_wit_2_pure := 
(
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition encrypt_partial_solve_wit_2_pure_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_89_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition encrypt_partial_solve_wit_2_aux := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
|--
  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_89_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition encrypt_partial_solve_wit_2 := encrypt_partial_solve_wit_2_pure -> encrypt_partial_solve_wit_2_aux.

Definition encrypt_partial_solve_wit_3 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_89_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (lowercase_codes_z_89 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (rotate_prefix_z_89 input output i ) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i output )
.

Definition encrypt_partial_solve_wit_4 := 
forall (s_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_89_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : (lowercase_codes_z_89 input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (rotate_prefix_z_89 input output i )) ,
  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i >= n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_89_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ (lowercase_codes_z_89 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (rotate_prefix_z_89 input output i ) ”
  &&  (((out + (n * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out n i (n + 1 ) )
  **  (CharArray.full out i output )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_encrypt_safety_wit_1 : encrypt_safety_wit_1.
Axiom proof_of_encrypt_safety_wit_2 : encrypt_safety_wit_2.
Axiom proof_of_encrypt_safety_wit_3 : encrypt_safety_wit_3.
Axiom proof_of_encrypt_safety_wit_4 : encrypt_safety_wit_4.
Axiom proof_of_encrypt_safety_wit_5 : encrypt_safety_wit_5.
Axiom proof_of_encrypt_safety_wit_6 : encrypt_safety_wit_6.
Axiom proof_of_encrypt_safety_wit_7 : encrypt_safety_wit_7.
Axiom proof_of_encrypt_safety_wit_8 : encrypt_safety_wit_8.
Axiom proof_of_encrypt_safety_wit_9 : encrypt_safety_wit_9.
Axiom proof_of_encrypt_safety_wit_10 : encrypt_safety_wit_10.
Axiom proof_of_encrypt_safety_wit_11 : encrypt_safety_wit_11.
Axiom proof_of_encrypt_safety_wit_12 : encrypt_safety_wit_12.
Axiom proof_of_encrypt_safety_wit_13 : encrypt_safety_wit_13.
Axiom proof_of_encrypt_safety_wit_14 : encrypt_safety_wit_14.
Axiom proof_of_encrypt_safety_wit_15 : encrypt_safety_wit_15.
Axiom proof_of_encrypt_entail_wit_1 : encrypt_entail_wit_1.
Axiom proof_of_encrypt_entail_wit_2 : encrypt_entail_wit_2.
Axiom proof_of_encrypt_return_wit_1 : encrypt_return_wit_1.
Axiom proof_of_encrypt_partial_solve_wit_1_pure : encrypt_partial_solve_wit_1_pure.
Axiom proof_of_encrypt_partial_solve_wit_1 : encrypt_partial_solve_wit_1.
Axiom proof_of_encrypt_partial_solve_wit_2_pure : encrypt_partial_solve_wit_2_pure.
Axiom proof_of_encrypt_partial_solve_wit_2 : encrypt_partial_solve_wit_2.
Axiom proof_of_encrypt_partial_solve_wit_3 : encrypt_partial_solve_wit_3.
Axiom proof_of_encrypt_partial_solve_wit_4 : encrypt_partial_solve_wit_4.

End VC_Correct.
