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
Require Import coins_140.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function fix_spaces -----*)

Definition fix_spaces_safety_wit_1 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_140_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string text_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition fix_spaces_safety_wit_2 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_140_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string text_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_3 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (valid_string input )) (PreH5 : (problem_140_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_4 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ False ”
.

Definition fix_spaces_safety_wit_5 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_6 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "spacelen" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_7 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_8 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= k)) (PreH6 : (0 <= spacelen)) (PreH7 : ((k + spacelen ) <= i)) (PreH8 : (k = (Zlength (output)))) (PreH9 : (fix_spaces_state_z_140 input output i spacelen )) (PreH10 : (valid_string input )) (PreH11 : (problem_140_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition fix_spaces_safety_wit_9 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (0 <= spacelen)) (PreH8 : ((k + spacelen ) <= i)) (PreH9 : (k = (Zlength (output)))) (PreH10 : (fix_spaces_state_z_140 input output i spacelen )) (PreH11 : (valid_string input )) (PreH12 : (problem_140_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ ((spacelen + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (spacelen + 1 )) ”
.

Definition fix_spaces_safety_wit_10 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (0 <= spacelen)) (PreH8 : ((k + spacelen ) <= i)) (PreH9 : (k = (Zlength (output)))) (PreH10 : (fix_spaces_state_z_140 input output i spacelen )) (PreH11 : (valid_string input )) (PreH12 : (problem_140_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_11 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (0 <= spacelen)) (PreH8 : ((k + spacelen ) <= i)) (PreH9 : (k = (Zlength (output)))) (PreH10 : (fix_spaces_state_z_140 input output i spacelen )) (PreH11 : (valid_string input )) (PreH12 : (problem_140_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_12 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 1)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (95 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 95) ”
.

Definition fix_spaces_safety_wit_13 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 1)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition fix_spaces_safety_wit_14 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 1)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_15 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 1)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_16 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <> 1)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_17 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 2)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ False ”
.

Definition fix_spaces_safety_wit_18 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 2)) (PreH2 : (spacelen <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (95 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 95) ”
.

Definition fix_spaces_safety_wit_19 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition fix_spaces_safety_wit_20 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_21 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (95 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 95) ”
.

Definition fix_spaces_safety_wit_22 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition fix_spaces_safety_wit_23 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_24 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_25 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <> 2)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_26 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <> 2)) (PreH2 : (spacelen <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_27 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (0 <= (k + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ False ”
.

Definition fix_spaces_safety_wit_28 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ False ”
.

Definition fix_spaces_safety_wit_29 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (45 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 45) ”
.

Definition fix_spaces_safety_wit_30 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition fix_spaces_safety_wit_31 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_32 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_33 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (0 <= (k + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_34 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_35 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_safety_wit_36 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen > 2)) (PreH4 : (spacelen <> 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (45) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition fix_spaces_safety_wit_37 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen > 2)) (PreH4 : (spacelen <> 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (45) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_38 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((k + 1 ) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (0 <= (k + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 2)) (PreH6 : (spacelen <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (0 <= k)) (PreH13 : (0 <= spacelen)) (PreH14 : ((k + spacelen ) <= i)) (PreH15 : (k = (Zlength (output)))) (PreH16 : (fix_spaces_state_z_140 input output i spacelen )) (PreH17 : (valid_string input )) (PreH18 : (problem_140_pre_z input )) (PreH19 : (ascii_range_z input )) (PreH20 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((((k + 1 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((k + 1 ) + 1 ) + 1 )) ”
.

Definition fix_spaces_safety_wit_39 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((k + 1 ) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (0 <= (k + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 2)) (PreH6 : (spacelen <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (0 <= k)) (PreH13 : (0 <= spacelen)) (PreH14 : ((k + spacelen ) <= i)) (PreH15 : (k = (Zlength (output)))) (PreH16 : (fix_spaces_state_z_140 input output i spacelen )) (PreH17 : (valid_string input )) (PreH18 : (problem_140_pre_z input )) (PreH19 : (ascii_range_z input )) (PreH20 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_40 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition fix_spaces_safety_wit_41 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_42 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition fix_spaces_safety_wit_43 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_44 := 
forall (text_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (k: Z) (spacelen: Z) (out: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= k)) (PreH5 : (0 <= spacelen)) (PreH6 : ((k + spacelen ) <= (i + 1 ))) (PreH7 : (k = (Zlength (output)))) (PreH8 : (fix_spaces_state_z_140 input output (i + 1 ) spacelen )) (PreH9 : (valid_string input )) (PreH10 : (problem_140_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fix_spaces_safety_wit_45 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= k)) (PreH6 : (0 <= spacelen)) (PreH7 : ((k + spacelen ) <= i)) (PreH8 : (k = (Zlength (output)))) (PreH9 : (fix_spaces_state_z_140 input output i spacelen )) (PreH10 : (valid_string input )) (PreH11 : (problem_140_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_46 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 1)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (0 <= spacelen)) (PreH8 : ((k + spacelen ) <= i)) (PreH9 : (k = (Zlength (output)))) (PreH10 : (fix_spaces_state_z_140 input output i spacelen )) (PreH11 : (valid_string input )) (PreH12 : (problem_140_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (95 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 95) ”
.

Definition fix_spaces_safety_wit_47 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 1)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition fix_spaces_safety_wit_48 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 1)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_49 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 1)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_50 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <> 1)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (0 <= spacelen)) (PreH8 : ((k + spacelen ) <= i)) (PreH9 : (k = (Zlength (output)))) (PreH10 : (fix_spaces_state_z_140 input output i spacelen )) (PreH11 : (valid_string input )) (PreH12 : (problem_140_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_51 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 2)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ False ”
.

Definition fix_spaces_safety_wit_52 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 2)) (PreH2 : (spacelen <> 1)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (95 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 95) ”
.

Definition fix_spaces_safety_wit_53 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition fix_spaces_safety_wit_54 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_55 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (95 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 95) ”
.

Definition fix_spaces_safety_wit_56 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((k + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k + 1 ) + 1 )) ”
.

Definition fix_spaces_safety_wit_57 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_58 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_59 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <> 2)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen = 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_60 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <> 2)) (PreH2 : (spacelen <> 1)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fix_spaces_safety_wit_61 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (0 <= (k + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 2)) (PreH5 : (spacelen <> 1)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ False ”
.

Definition fix_spaces_safety_wit_62 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ False ”
.

Definition fix_spaces_safety_wit_63 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (spacelen <> 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (45 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 45) ”
.

Definition fix_spaces_safety_wit_64 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition fix_spaces_safety_wit_65 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fix_spaces_safety_wit_66 := 
forall (text_pre: Z) (input: (@list Z)) (prefix: (@list Z)) (output: (@list Z)) (i: Z) (n: Z) (k: Z) (spacelen: Z) (out: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= k)) (PreH3 : (0 <= spacelen)) (PreH4 : (k <= n)) (PreH5 : (k = (Zlength (output)))) (PreH6 : (output = (app (prefix) ((flush_spaces_z_140 (spacelen)))))) (PreH7 : (fix_spaces_state_z_140 input prefix n spacelen )) (PreH8 : (valid_string input )) (PreH9 : (problem_140_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (store_string text_pre input )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fix_spaces_entail_wit_1 := 
(
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (retval = (string_length (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 0 ) <= 0) ” 
  &&  “ (0 = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output 0 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full retval_2 0 output )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
) \/
(
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (fix_spaces_state_z_140 input (@nil Z) 0 0 ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
).

Definition fix_spaces_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (fix_spaces_state_z_140 input (@nil Z) 0 0 ) ”
.

Definition fix_spaces_entail_wit_1_split_goal_2 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition fix_spaces_entail_wit_1_split_goal_3 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (0 <= retval) ”
.

Definition fix_spaces_entail_wit_1_split_goal_spatial := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  (CharArray.undef_full retval_2 (retval + 1 ) )
.

Definition fix_spaces_entail_wit_2_1 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output_2)))) (PreH14 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (((k + 1 ) + 0 ) <= (i + 1 )) ” 
  &&  “ ((k + 1 ) = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output (i + 1 ) 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out (k + 1 ) output )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output_2)))) (PreH14 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ” 
  &&  “ ((k + 1 ) = (Zlength ((app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition fix_spaces_entail_wit_2_1_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output_2)))) (PreH14 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ”
.

Definition fix_spaces_entail_wit_2_1_split_goal_2 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output_2)))) (PreH14 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ ((k + 1 ) = (Zlength ((app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
.

Definition fix_spaces_entail_wit_2_2 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((((k + 1 ) + 1 ) + 0 ) <= (i + 1 )) ” 
  &&  “ (((k + 1 ) + 1 ) = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output (i + 1 ) 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out ((k + 1 ) + 1 ) output )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ” 
  &&  “ (((k + 1 ) + 1 ) = (Zlength ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition fix_spaces_entail_wit_2_2_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ”
.

Definition fix_spaces_entail_wit_2_2_split_goal_2 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (((k + 1 ) + 1 ) = (Zlength ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
.

Definition fix_spaces_entail_wit_2_3 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((k + 1 ) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (0 <= (k + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 2)) (PreH6 : (spacelen <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (0 <= k)) (PreH13 : (0 <= spacelen)) (PreH14 : ((k + spacelen ) <= i)) (PreH15 : (k = (Zlength (output_2)))) (PreH16 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH17 : (valid_string input )) (PreH18 : (problem_140_pre_z input )) (PreH19 : (ascii_range_z input )) (PreH20 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (((k + 1 ) + 1 ) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (((((k + 1 ) + 1 ) + 1 ) + 0 ) <= (i + 1 )) ” 
  &&  “ ((((k + 1 ) + 1 ) + 1 ) = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output (i + 1 ) 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) output )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((k + 1 ) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (0 <= (k + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 2)) (PreH6 : (spacelen <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (0 <= k)) (PreH13 : (0 <= spacelen)) (PreH14 : ((k + spacelen ) <= i)) (PreH15 : (k = (Zlength (output_2)))) (PreH16 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH17 : (valid_string input )) (PreH18 : (problem_140_pre_z input )) (PreH19 : (ascii_range_z input )) (PreH20 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ” 
  &&  “ ((((k + 1 ) + 1 ) + 1 ) = (Zlength ((app ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition fix_spaces_entail_wit_2_3_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((k + 1 ) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (0 <= (k + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 2)) (PreH6 : (spacelen <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (0 <= k)) (PreH13 : (0 <= spacelen)) (PreH14 : ((k + spacelen ) <= i)) (PreH15 : (k = (Zlength (output_2)))) (PreH16 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH17 : (valid_string input )) (PreH18 : (problem_140_pre_z input )) (PreH19 : (ascii_range_z input )) (PreH20 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ”
.

Definition fix_spaces_entail_wit_2_3_split_goal_2 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((k + 1 ) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (0 <= (k + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 2)) (PreH6 : (spacelen <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (0 <= k)) (PreH13 : (0 <= spacelen)) (PreH14 : ((k + spacelen ) <= i)) (PreH15 : (k = (Zlength (output_2)))) (PreH16 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH17 : (valid_string input )) (PreH18 : (problem_140_pre_z input )) (PreH19 : (ascii_range_z input )) (PreH20 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ ((((k + 1 ) + 1 ) + 1 ) = (Zlength ((app ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
.

Definition fix_spaces_entail_wit_2_4 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen > 2)) (PreH4 : (spacelen <> 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output_2) ((cons (45) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((((k + 1 ) + 1 ) + 0 ) <= (i + 1 )) ” 
  &&  “ (((k + 1 ) + 1 ) = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output (i + 1 ) 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out ((k + 1 ) + 1 ) output )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen > 2)) (PreH4 : (spacelen <> 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app ((app (output_2) ((cons (45) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ” 
  &&  “ (((k + 1 ) + 1 ) = (Zlength ((app ((app (output_2) ((cons (45) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition fix_spaces_entail_wit_2_4_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen > 2)) (PreH4 : (spacelen <> 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input (app ((app (output_2) ((cons (45) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) 0 ) ”
.

Definition fix_spaces_entail_wit_2_4_split_goal_2 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen > 2)) (PreH4 : (spacelen <> 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output_2)))) (PreH15 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (((k + 1 ) + 1 ) = (Zlength ((app ((app (output_2) ((cons (45) ((@nil Z)))))) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z)))))))) ”
.

Definition fix_spaces_entail_wit_2_5 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (0 <= spacelen)) (PreH8 : ((k + spacelen ) <= i)) (PreH9 : (k = (Zlength (output_2)))) (PreH10 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH11 : (valid_string input )) (PreH12 : (problem_140_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output_2 )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= (spacelen + 1 )) ” 
  &&  “ ((k + (spacelen + 1 ) ) <= (i + 1 )) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output (i + 1 ) (spacelen + 1 ) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output_2)))) (PreH11 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input output_2 (i + 1 ) (spacelen + 1 ) ) ”
  &&  emp
).

Definition fix_spaces_entail_wit_2_5_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output_2)))) (PreH11 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fix_spaces_state_z_140 input output_2 (i + 1 ) (spacelen + 1 ) ) ”
.

Definition fix_spaces_entail_wit_3 := 
forall (text_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (k: Z) (spacelen: Z) (out: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= k)) (PreH5 : (0 <= spacelen)) (PreH6 : ((k + spacelen ) <= (i + 1 ))) (PreH7 : (k = (Zlength (output_2)))) (PreH8 : (fix_spaces_state_z_140 input output_2 (i + 1 ) spacelen )) (PreH9 : (valid_string input )) (PreH10 : (problem_140_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output_2 )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= (i + 1 )) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output (i + 1 ) spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
.

Definition fix_spaces_entail_wit_4_1 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (spacelen <> 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output_2)))) (PreH12 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output_2 )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  EX (prefix: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ (k <= n) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (output = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output_2)))) (PreH13 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  EX (prefix: (@list Z)) ,
  “ (output_2 = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ (k <= n) ” 
  &&  “ (k = (Zlength ((app (prefix) ((flush_spaces_z_140 (spacelen))))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  emp
).

Definition fix_spaces_entail_wit_4_2 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output_2)))) (PreH13 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output_2) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (prefix: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + 1 ) <= n) ” 
  &&  “ ((k + 1 ) = (Zlength (output))) ” 
  &&  “ (output = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out (k + 1 ) output )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output_2)))) (PreH13 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  EX (prefix: (@list Z)) ,
  “ ((app (output_2) ((cons (95) ((@nil Z))))) = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + 1 ) <= n) ” 
  &&  “ ((k + 1 ) = (Zlength ((app (prefix) ((flush_spaces_z_140 (spacelen))))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  emp
).

Definition fix_spaces_entail_wit_4_3 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (0 <= (k + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 2)) (PreH5 : (spacelen <> 1)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output_2)))) (PreH14 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (prefix: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ (((k + 1 ) + 1 ) <= n) ” 
  &&  “ (((k + 1 ) + 1 ) = (Zlength (output))) ” 
  &&  “ (output = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out ((k + 1 ) + 1 ) output )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (0 <= (k + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 2)) (PreH5 : (spacelen <> 1)) (PreH6 : (i >= n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output_2)))) (PreH14 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  EX (prefix: (@list Z)) ,
  “ ((app ((app (output_2) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ (((k + 1 ) + 1 ) <= n) ” 
  &&  “ (((k + 1 ) + 1 ) = (Zlength ((app (prefix) ((flush_spaces_z_140 (spacelen))))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  emp
).

Definition fix_spaces_entail_wit_4_4 := 
(
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output_2)))) (PreH13 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output_2) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (prefix: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + 1 ) <= n) ” 
  &&  “ ((k + 1 ) = (Zlength (output))) ” 
  &&  “ (output = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
  **  (CharArray.full out (k + 1 ) output )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : (i >= n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output_2)))) (PreH13 : (fix_spaces_state_z_140 input output_2 i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  EX (prefix: (@list Z)) ,
  “ ((app (output_2) ((cons (45) ((@nil Z))))) = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + 1 ) <= n) ” 
  &&  “ ((k + 1 ) = (Zlength ((app (prefix) ((flush_spaces_z_140 (spacelen))))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  emp
).

Definition fix_spaces_return_wit_1 := 
(
forall (text_pre: Z) (input: (@list Z)) (prefix: (@list Z)) (output_2: (@list Z)) (n: Z) (k: Z) (spacelen: Z) (out: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= k)) (PreH4 : (0 <= spacelen)) (PreH5 : (k <= n)) (PreH6 : (k = (Zlength (output_2)))) (PreH7 : (output_2 = (app (prefix) ((flush_spaces_z_140 (spacelen)))))) (PreH8 : (fix_spaces_state_z_140 input prefix n spacelen )) (PreH9 : (valid_string input )) (PreH10 : (problem_140_pre_z input )) (PreH11 : (ascii_range_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_140_spec_z input output ) ”
  &&  (store_string text_pre input )
  **  (store_string out output )
  **  (CharArray.undef_seg out ((string_length (output)) + 1 ) ((string_length (input)) + 1 ) )
) \/
(
forall (input: (@list Z)) (prefix: (@list Z)) (output_2: (@list Z)) (n: Z) (k: Z) (spacelen: Z) (out: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= k)) (PreH5 : (0 <= spacelen)) (PreH6 : (k <= n)) (PreH7 : (k = (Zlength (output_2)))) (PreH8 : (output_2 = (app (prefix) ((flush_spaces_z_140 (spacelen)))))) (PreH9 : (fix_spaces_state_z_140 input prefix n spacelen )) (PreH10 : (valid_string input )) (PreH11 : (problem_140_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (problem_140_spec_z input output ) ”
  &&  (CharArray.full out ((string_length (output)) + 1 ) (c_string (output)) )
  **  (CharArray.undef_seg out ((string_length (output)) + 1 ) ((string_length (input)) + 1 ) )
).

Definition fix_spaces_partial_solve_wit_1_pure := 
forall (text_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_140_pre_z input )) (PreH3 : (ascii_range_z input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition fix_spaces_partial_solve_wit_1_aux := 
forall (text_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_140_pre_z input )) (PreH3 : (ascii_range_z input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string text_pre input )
.

Definition fix_spaces_partial_solve_wit_1 := fix_spaces_partial_solve_wit_1_pure -> fix_spaces_partial_solve_wit_1_aux.

Definition fix_spaces_partial_solve_wit_2_pure := 
(
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_140_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string text_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ”
) \/
(
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition fix_spaces_partial_solve_wit_2_pure_split_goal_1 := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_140_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition fix_spaces_partial_solve_wit_2_aux := 
forall (text_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_140_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition fix_spaces_partial_solve_wit_2 := fix_spaces_partial_solve_wit_2_pure -> fix_spaces_partial_solve_wit_2_aux.

Definition fix_spaces_partial_solve_wit_3 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 1)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Definition fix_spaces_partial_solve_wit_4 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 2)) (PreH2 : (spacelen <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Definition fix_spaces_partial_solve_wit_5 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (n + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition fix_spaces_partial_solve_wit_6 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen > 2) ” 
  &&  “ (spacelen <> 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Definition fix_spaces_partial_solve_wit_7 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen > 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (spacelen <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen > 2) ” 
  &&  “ (spacelen <> 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  (CharArray.missing_i text_pre i 0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
.

Definition fix_spaces_partial_solve_wit_8 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (spacelen > 2)) (PreH4 : (spacelen <> 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen > 2) ” 
  &&  “ (spacelen <> 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (45) ((@nil Z))))) )
.

Definition fix_spaces_partial_solve_wit_9 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (0 <= (k + 1 ))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 2)) (PreH5 : (spacelen <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (0 <= ((k + 1 ) + 1 )) ” 
  &&  “ (spacelen <= 2) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  (CharArray.missing_i text_pre i 0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
.

Definition fix_spaces_partial_solve_wit_10 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((k + 1 ) + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (0 <= (k + 1 ))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 2)) (PreH6 : (spacelen <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (0 <= k)) (PreH13 : (0 <= spacelen)) (PreH14 : ((k + spacelen ) <= i)) (PreH15 : (k = (Zlength (output)))) (PreH16 : (fix_spaces_state_z_140 input output i spacelen )) (PreH17 : (valid_string input )) (PreH18 : (problem_140_pre_z input )) (PreH19 : (ascii_range_z input )) (PreH20 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (n + 1 ) )
|--
  “ (0 <= ((k + 1 ) + 1 )) ” 
  &&  “ (spacelen <= 2) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (((k + 1 ) + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out ((k + 1 ) + 1 ) ((k + 1 ) + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (output) ((cons (95) ((@nil Z)))))) ((cons (95) ((@nil Z))))) )
.

Definition fix_spaces_partial_solve_wit_11 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (spacelen = 1)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= k)) (PreH11 : (0 <= spacelen)) (PreH12 : ((k + spacelen ) <= i)) (PreH13 : (k = (Zlength (output)))) (PreH14 : (fix_spaces_state_z_140 input output i spacelen )) (PreH15 : (valid_string input )) (PreH16 : (problem_140_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (spacelen <= 2) ” 
  &&  “ (spacelen <> 2) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  (CharArray.missing_i text_pre i 0 ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
.

Definition fix_spaces_partial_solve_wit_12 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (spacelen <= 2)) (PreH3 : (spacelen <> 2)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (spacelen = 1)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= k)) (PreH12 : (0 <= spacelen)) (PreH13 : ((k + spacelen ) <= i)) (PreH14 : (k = (Zlength (output)))) (PreH15 : (fix_spaces_state_z_140 input output i spacelen )) (PreH16 : (valid_string input )) (PreH17 : (problem_140_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (spacelen <= 2) ” 
  &&  “ (spacelen <> 2) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
.

Definition fix_spaces_partial_solve_wit_13 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen <= 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (spacelen <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (0 <= spacelen)) (PreH11 : ((k + spacelen ) <= i)) (PreH12 : (k = (Zlength (output)))) (PreH13 : (fix_spaces_state_z_140 input output i spacelen )) (PreH14 : (valid_string input )) (PreH15 : (problem_140_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen <= 2) ” 
  &&  “ (spacelen <> 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Definition fix_spaces_partial_solve_wit_14 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 1)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= k)) (PreH7 : (0 <= spacelen)) (PreH8 : ((k + spacelen ) <= i)) (PreH9 : (k = (Zlength (output)))) (PreH10 : (fix_spaces_state_z_140 input output i spacelen )) (PreH11 : (valid_string input )) (PreH12 : (problem_140_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 1) ” 
  &&  “ (i >= n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Definition fix_spaces_partial_solve_wit_15 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen = 2)) (PreH2 : (spacelen <> 1)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= k)) (PreH8 : (0 <= spacelen)) (PreH9 : ((k + spacelen ) <= i)) (PreH10 : (k = (Zlength (output)))) (PreH11 : (fix_spaces_state_z_140 input output i spacelen )) (PreH12 : (valid_string input )) (PreH13 : (problem_140_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ (i >= n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Definition fix_spaces_partial_solve_wit_16 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (spacelen = 2)) (PreH3 : (spacelen <> 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (n + 1 ) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen = 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ (i >= n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (n + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (output) ((cons (95) ((@nil Z))))) )
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition fix_spaces_partial_solve_wit_17 := 
forall (text_pre: Z) (input: (@list Z)) (out: Z) (output: (@list Z)) (spacelen: Z) (k: Z) (i: Z) (n: Z) (PreH1 : (spacelen > 2)) (PreH2 : (spacelen <> 2)) (PreH3 : (spacelen <> 1)) (PreH4 : (i >= n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (0 <= spacelen)) (PreH10 : ((k + spacelen ) <= i)) (PreH11 : (k = (Zlength (output)))) (PreH12 : (fix_spaces_state_z_140 input output i spacelen )) (PreH13 : (valid_string input )) (PreH14 : (problem_140_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (spacelen > 2) ” 
  &&  “ (spacelen <> 2) ” 
  &&  “ (spacelen <> 1) ” 
  &&  “ (i >= n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ ((k + spacelen ) <= i) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (fix_spaces_state_z_140 input output i spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Definition fix_spaces_partial_solve_wit_18 := 
forall (text_pre: Z) (input: (@list Z)) (prefix: (@list Z)) (output: (@list Z)) (n: Z) (k: Z) (spacelen: Z) (out: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= k)) (PreH3 : (0 <= spacelen)) (PreH4 : (k <= n)) (PreH5 : (k = (Zlength (output)))) (PreH6 : (output = (app (prefix) ((flush_spaces_z_140 (spacelen)))))) (PreH7 : (fix_spaces_state_z_140 input prefix n spacelen )) (PreH8 : (valid_string input )) (PreH9 : (problem_140_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) ,
  (store_string text_pre input )
  **  (CharArray.full out k output )
  **  (CharArray.undef_seg out k (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= spacelen) ” 
  &&  “ (k <= n) ” 
  &&  “ (k = (Zlength (output))) ” 
  &&  “ (output = (app (prefix) ((flush_spaces_z_140 (spacelen))))) ” 
  &&  “ (fix_spaces_state_z_140 input prefix n spacelen ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_140_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full text_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out k k (n + 1 ) )
  **  (CharArray.full out k output )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_fix_spaces_safety_wit_1 : fix_spaces_safety_wit_1.
Axiom proof_of_fix_spaces_safety_wit_2 : fix_spaces_safety_wit_2.
Axiom proof_of_fix_spaces_safety_wit_3 : fix_spaces_safety_wit_3.
Axiom proof_of_fix_spaces_safety_wit_4 : fix_spaces_safety_wit_4.
Axiom proof_of_fix_spaces_safety_wit_5 : fix_spaces_safety_wit_5.
Axiom proof_of_fix_spaces_safety_wit_6 : fix_spaces_safety_wit_6.
Axiom proof_of_fix_spaces_safety_wit_7 : fix_spaces_safety_wit_7.
Axiom proof_of_fix_spaces_safety_wit_8 : fix_spaces_safety_wit_8.
Axiom proof_of_fix_spaces_safety_wit_9 : fix_spaces_safety_wit_9.
Axiom proof_of_fix_spaces_safety_wit_10 : fix_spaces_safety_wit_10.
Axiom proof_of_fix_spaces_safety_wit_11 : fix_spaces_safety_wit_11.
Axiom proof_of_fix_spaces_safety_wit_12 : fix_spaces_safety_wit_12.
Axiom proof_of_fix_spaces_safety_wit_13 : fix_spaces_safety_wit_13.
Axiom proof_of_fix_spaces_safety_wit_14 : fix_spaces_safety_wit_14.
Axiom proof_of_fix_spaces_safety_wit_15 : fix_spaces_safety_wit_15.
Axiom proof_of_fix_spaces_safety_wit_16 : fix_spaces_safety_wit_16.
Axiom proof_of_fix_spaces_safety_wit_17 : fix_spaces_safety_wit_17.
Axiom proof_of_fix_spaces_safety_wit_18 : fix_spaces_safety_wit_18.
Axiom proof_of_fix_spaces_safety_wit_19 : fix_spaces_safety_wit_19.
Axiom proof_of_fix_spaces_safety_wit_20 : fix_spaces_safety_wit_20.
Axiom proof_of_fix_spaces_safety_wit_21 : fix_spaces_safety_wit_21.
Axiom proof_of_fix_spaces_safety_wit_22 : fix_spaces_safety_wit_22.
Axiom proof_of_fix_spaces_safety_wit_23 : fix_spaces_safety_wit_23.
Axiom proof_of_fix_spaces_safety_wit_24 : fix_spaces_safety_wit_24.
Axiom proof_of_fix_spaces_safety_wit_25 : fix_spaces_safety_wit_25.
Axiom proof_of_fix_spaces_safety_wit_26 : fix_spaces_safety_wit_26.
Axiom proof_of_fix_spaces_safety_wit_27 : fix_spaces_safety_wit_27.
Axiom proof_of_fix_spaces_safety_wit_28 : fix_spaces_safety_wit_28.
Axiom proof_of_fix_spaces_safety_wit_29 : fix_spaces_safety_wit_29.
Axiom proof_of_fix_spaces_safety_wit_30 : fix_spaces_safety_wit_30.
Axiom proof_of_fix_spaces_safety_wit_31 : fix_spaces_safety_wit_31.
Axiom proof_of_fix_spaces_safety_wit_32 : fix_spaces_safety_wit_32.
Axiom proof_of_fix_spaces_safety_wit_33 : fix_spaces_safety_wit_33.
Axiom proof_of_fix_spaces_safety_wit_34 : fix_spaces_safety_wit_34.
Axiom proof_of_fix_spaces_safety_wit_35 : fix_spaces_safety_wit_35.
Axiom proof_of_fix_spaces_safety_wit_36 : fix_spaces_safety_wit_36.
Axiom proof_of_fix_spaces_safety_wit_37 : fix_spaces_safety_wit_37.
Axiom proof_of_fix_spaces_safety_wit_38 : fix_spaces_safety_wit_38.
Axiom proof_of_fix_spaces_safety_wit_39 : fix_spaces_safety_wit_39.
Axiom proof_of_fix_spaces_safety_wit_40 : fix_spaces_safety_wit_40.
Axiom proof_of_fix_spaces_safety_wit_41 : fix_spaces_safety_wit_41.
Axiom proof_of_fix_spaces_safety_wit_42 : fix_spaces_safety_wit_42.
Axiom proof_of_fix_spaces_safety_wit_43 : fix_spaces_safety_wit_43.
Axiom proof_of_fix_spaces_safety_wit_44 : fix_spaces_safety_wit_44.
Axiom proof_of_fix_spaces_safety_wit_45 : fix_spaces_safety_wit_45.
Axiom proof_of_fix_spaces_safety_wit_46 : fix_spaces_safety_wit_46.
Axiom proof_of_fix_spaces_safety_wit_47 : fix_spaces_safety_wit_47.
Axiom proof_of_fix_spaces_safety_wit_48 : fix_spaces_safety_wit_48.
Axiom proof_of_fix_spaces_safety_wit_49 : fix_spaces_safety_wit_49.
Axiom proof_of_fix_spaces_safety_wit_50 : fix_spaces_safety_wit_50.
Axiom proof_of_fix_spaces_safety_wit_51 : fix_spaces_safety_wit_51.
Axiom proof_of_fix_spaces_safety_wit_52 : fix_spaces_safety_wit_52.
Axiom proof_of_fix_spaces_safety_wit_53 : fix_spaces_safety_wit_53.
Axiom proof_of_fix_spaces_safety_wit_54 : fix_spaces_safety_wit_54.
Axiom proof_of_fix_spaces_safety_wit_55 : fix_spaces_safety_wit_55.
Axiom proof_of_fix_spaces_safety_wit_56 : fix_spaces_safety_wit_56.
Axiom proof_of_fix_spaces_safety_wit_57 : fix_spaces_safety_wit_57.
Axiom proof_of_fix_spaces_safety_wit_58 : fix_spaces_safety_wit_58.
Axiom proof_of_fix_spaces_safety_wit_59 : fix_spaces_safety_wit_59.
Axiom proof_of_fix_spaces_safety_wit_60 : fix_spaces_safety_wit_60.
Axiom proof_of_fix_spaces_safety_wit_61 : fix_spaces_safety_wit_61.
Axiom proof_of_fix_spaces_safety_wit_62 : fix_spaces_safety_wit_62.
Axiom proof_of_fix_spaces_safety_wit_63 : fix_spaces_safety_wit_63.
Axiom proof_of_fix_spaces_safety_wit_64 : fix_spaces_safety_wit_64.
Axiom proof_of_fix_spaces_safety_wit_65 : fix_spaces_safety_wit_65.
Axiom proof_of_fix_spaces_safety_wit_66 : fix_spaces_safety_wit_66.
Axiom proof_of_fix_spaces_entail_wit_1 : fix_spaces_entail_wit_1.
Axiom proof_of_fix_spaces_entail_wit_2_1 : fix_spaces_entail_wit_2_1.
Axiom proof_of_fix_spaces_entail_wit_2_2 : fix_spaces_entail_wit_2_2.
Axiom proof_of_fix_spaces_entail_wit_2_3 : fix_spaces_entail_wit_2_3.
Axiom proof_of_fix_spaces_entail_wit_2_4 : fix_spaces_entail_wit_2_4.
Axiom proof_of_fix_spaces_entail_wit_2_5 : fix_spaces_entail_wit_2_5.
Axiom proof_of_fix_spaces_entail_wit_3 : fix_spaces_entail_wit_3.
Axiom proof_of_fix_spaces_entail_wit_4_1 : fix_spaces_entail_wit_4_1.
Axiom proof_of_fix_spaces_entail_wit_4_2 : fix_spaces_entail_wit_4_2.
Axiom proof_of_fix_spaces_entail_wit_4_3 : fix_spaces_entail_wit_4_3.
Axiom proof_of_fix_spaces_entail_wit_4_4 : fix_spaces_entail_wit_4_4.
Axiom proof_of_fix_spaces_return_wit_1 : fix_spaces_return_wit_1.
Axiom proof_of_fix_spaces_partial_solve_wit_1_pure : fix_spaces_partial_solve_wit_1_pure.
Axiom proof_of_fix_spaces_partial_solve_wit_1 : fix_spaces_partial_solve_wit_1.
Axiom proof_of_fix_spaces_partial_solve_wit_2_pure : fix_spaces_partial_solve_wit_2_pure.
Axiom proof_of_fix_spaces_partial_solve_wit_2 : fix_spaces_partial_solve_wit_2.
Axiom proof_of_fix_spaces_partial_solve_wit_3 : fix_spaces_partial_solve_wit_3.
Axiom proof_of_fix_spaces_partial_solve_wit_4 : fix_spaces_partial_solve_wit_4.
Axiom proof_of_fix_spaces_partial_solve_wit_5 : fix_spaces_partial_solve_wit_5.
Axiom proof_of_fix_spaces_partial_solve_wit_6 : fix_spaces_partial_solve_wit_6.
Axiom proof_of_fix_spaces_partial_solve_wit_7 : fix_spaces_partial_solve_wit_7.
Axiom proof_of_fix_spaces_partial_solve_wit_8 : fix_spaces_partial_solve_wit_8.
Axiom proof_of_fix_spaces_partial_solve_wit_9 : fix_spaces_partial_solve_wit_9.
Axiom proof_of_fix_spaces_partial_solve_wit_10 : fix_spaces_partial_solve_wit_10.
Axiom proof_of_fix_spaces_partial_solve_wit_11 : fix_spaces_partial_solve_wit_11.
Axiom proof_of_fix_spaces_partial_solve_wit_12 : fix_spaces_partial_solve_wit_12.
Axiom proof_of_fix_spaces_partial_solve_wit_13 : fix_spaces_partial_solve_wit_13.
Axiom proof_of_fix_spaces_partial_solve_wit_14 : fix_spaces_partial_solve_wit_14.
Axiom proof_of_fix_spaces_partial_solve_wit_15 : fix_spaces_partial_solve_wit_15.
Axiom proof_of_fix_spaces_partial_solve_wit_16 : fix_spaces_partial_solve_wit_16.
Axiom proof_of_fix_spaces_partial_solve_wit_17 : fix_spaces_partial_solve_wit_17.
Axiom proof_of_fix_spaces_partial_solve_wit_18 : fix_spaces_partial_solve_wit_18.

End VC_Correct.
