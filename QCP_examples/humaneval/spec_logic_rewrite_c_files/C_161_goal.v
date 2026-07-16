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
Require Import coins_161.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solve -----*)

Definition solve_safety_wit_1 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_161_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "nletter" ) )) # Int  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_2 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_161_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition solve_safety_wit_3 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_161_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_4 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (input)))) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (valid_string input )) (PreH5 : (problem_161_pre_z input )) (PreH6 : (ascii_range_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_5 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ False ”
.

Definition solve_safety_wit_6 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_7 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "w" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_8 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= nletter)) (PreH7 : (nletter <= i)) (PreH8 : (0 <= w)) (PreH9 : (w <= 127)) (PreH10 : (flip_scan_state_z_161 input output i nletter )) (PreH11 : (valid_string input )) (PreH12 : (problem_161_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition solve_safety_wit_9 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) >= 65)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (out <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= nletter)) (PreH8 : (nletter <= i)) (PreH9 : (0 <= w)) (PreH10 : (w <= 127)) (PreH11 : (flip_scan_state_z_161 input output i nletter )) (PreH12 : (valid_string input )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition solve_safety_wit_10 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (input)) 0) + 32 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (input)) 0) + 32 )) ”
.

Definition solve_safety_wit_11 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition solve_safety_wit_12 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 65)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (out <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= nletter)) (PreH8 : (nletter <= i)) (PreH9 : (0 <= w)) (PreH10 : (w <= 127)) (PreH11 : (flip_scan_state_z_161 input output i nletter )) (PreH12 : (valid_string input )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solve_safety_wit_13 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) > 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solve_safety_wit_14 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) >= 97)) (PreH2 : ((Znth i (c_string (input)) 0) < 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ False ”
.

Definition solve_safety_wit_15 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) >= 97)) (PreH2 : ((Znth i (c_string (input)) 0) > 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition solve_safety_wit_16 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 122)) (PreH2 : ((Znth i (c_string (input)) 0) >= 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (input)) 0) - 32 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (input)) 0) - 32 )) ”
.

Definition solve_safety_wit_17 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 122)) (PreH2 : ((Znth i (c_string (input)) 0) >= 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition solve_safety_wit_18 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 97)) (PreH2 : ((Znth i (c_string (input)) 0) > 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((nletter + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nletter + 1 )) ”
.

Definition solve_safety_wit_19 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 97)) (PreH2 : ((Znth i (c_string (input)) 0) > 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_20 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 97)) (PreH2 : ((Znth i (c_string (input)) 0) < 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((nletter + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nletter + 1 )) ”
.

Definition solve_safety_wit_21 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 97)) (PreH2 : ((Znth i (c_string (input)) 0) < 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_22 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) > 122)) (PreH2 : ((Znth i (c_string (input)) 0) >= 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((nletter + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nletter + 1 )) ”
.

Definition solve_safety_wit_23 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) > 122)) (PreH2 : ((Znth i (c_string (input)) 0) >= 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_24 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (out: Z) (i: Z) (nletter: Z) (w: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= nletter)) (PreH6 : (nletter <= (i + 1 ))) (PreH7 : (0 <= w)) (PreH8 : (w <= 127)) (PreH9 : (flip_scan_state_z_161 input output (i + 1 ) nletter )) (PreH10 : (valid_string input )) (PreH11 : (problem_161_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_25 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (0 <= nletter)) (PreH5 : (nletter <= n)) (PreH6 : (flip_scan_state_z_161 input output n nletter )) (PreH7 : (valid_string input )) (PreH8 : (problem_161_pre_z input )) (PreH9 : (ascii_range_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (store_string s_pre input )
  **  (CharArray.full out n output )
  **  (CharArray.undef_seg out n (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_26 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (nletter = n)) (PreH5 : (no_letter_z_161 input )) (PreH6 : (flip_output_z_161 input output )) (PreH7 : (valid_string input )) (PreH8 : (valid_string output )) (PreH9 : (problem_161_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition solve_safety_wit_27 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (nletter = n)) (PreH5 : (no_letter_z_161 input )) (PreH6 : (flip_output_z_161 input output )) (PreH7 : (valid_string input )) (PreH8 : (valid_string output )) (PreH9 : (problem_161_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_28 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (out <> 0)) (PreH7 : (nletter = n)) (PreH8 : (no_letter_z_161 input )) (PreH9 : (flip_output_z_161 input output )) (PreH10 : (valid_string input )) (PreH11 : (valid_string output )) (PreH12 : (problem_161_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_29 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (i = n)) (PreH7 : (out <> 0)) (PreH8 : (nletter = n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output )) (PreH11 : (valid_string input )) (PreH12 : (valid_string output )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ False ”
.

Definition solve_safety_wit_30 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (i = n)) (PreH7 : (out <> 0)) (PreH8 : (nletter = n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output )) (PreH11 : (valid_string input )) (PreH12 : (valid_string output )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (CharArray.undef_full retval (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_31 := 
forall (s_pre: Z) (input: (@list Z)) (rev_output: (@list Z)) (output: (@list Z)) (j: Z) (w: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (j < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (i = n)) (PreH4 : (out <> 0)) (PreH5 : (p <> 0)) (PreH6 : (nletter = n)) (PreH7 : (0 <= j)) (PreH8 : (j <= n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output )) (PreH11 : (reverse_scan_state_z_161 input rev_output j )) (PreH12 : (valid_string input )) (PreH13 : (valid_string output )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p j rev_output )
  **  (CharArray.undef_seg p j (n + 1 ) )
|--
  “ (((n - 1 ) - j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n - 1 ) - j )) ”
.

Definition solve_safety_wit_32 := 
forall (s_pre: Z) (input: (@list Z)) (rev_output: (@list Z)) (output: (@list Z)) (j: Z) (w: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (j < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (i = n)) (PreH4 : (out <> 0)) (PreH5 : (p <> 0)) (PreH6 : (nletter = n)) (PreH7 : (0 <= j)) (PreH8 : (j <= n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output )) (PreH11 : (reverse_scan_state_z_161 input rev_output j )) (PreH12 : (valid_string input )) (PreH13 : (valid_string output )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p j rev_output )
  **  (CharArray.undef_seg p j (n + 1 ) )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition solve_safety_wit_33 := 
forall (s_pre: Z) (input: (@list Z)) (rev_output: (@list Z)) (output: (@list Z)) (j: Z) (w: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (j < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (i = n)) (PreH4 : (out <> 0)) (PreH5 : (p <> 0)) (PreH6 : (nletter = n)) (PreH7 : (0 <= j)) (PreH8 : (j <= n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output )) (PreH11 : (reverse_scan_state_z_161 input rev_output j )) (PreH12 : (valid_string input )) (PreH13 : (valid_string output )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p j rev_output )
  **  (CharArray.undef_seg p j (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_34 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (out: Z) (p: Z) (nletter: Z) (w: Z) (j: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (p <> 0)) (PreH5 : (nletter = n)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (no_letter_z_161 input )) (PreH9 : (flip_output_z_161 input output )) (PreH10 : (reverse_scan_state_z_161 input rev_output (j + 1 ) )) (PreH11 : (valid_string input )) (PreH12 : (valid_string output )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p (j + 1 ) rev_output )
  **  (CharArray.undef_seg p (j + 1 ) (n + 1 ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solve_safety_wit_35 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (w: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (j = n)) (PreH4 : (out <> 0)) (PreH5 : (p <> 0)) (PreH6 : (nletter = n)) (PreH7 : (no_letter_z_161 input )) (PreH8 : (flip_output_z_161 input output )) (PreH9 : (reverse_output_z_161 input rev_output )) (PreH10 : (valid_string input )) (PreH11 : (valid_string output )) (PreH12 : (valid_string rev_output )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (problem_161_spec_z input rev_output )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p n rev_output )
  **  (CharArray.undef_seg p n (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_36 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (w: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= n)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (j = n)) (PreH7 : (out <> 0)) (PreH8 : (p <> 0)) (PreH9 : (nletter = n)) (PreH10 : (no_letter_z_161 input )) (PreH11 : (flip_output_z_161 input output )) (PreH12 : (reverse_output_z_161 input rev_output )) (PreH13 : (valid_string input )) (PreH14 : (valid_string output )) (PreH15 : (valid_string rev_output )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (problem_161_spec_z input rev_output )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p (n + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition solve_safety_wit_37 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (w: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= n)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (j = n)) (PreH7 : (out <> 0)) (PreH8 : (p <> 0)) (PreH9 : (nletter = n)) (PreH10 : (no_letter_z_161 input )) (PreH11 : (flip_output_z_161 input output )) (PreH12 : (reverse_output_z_161 input rev_output )) (PreH13 : (valid_string input )) (PreH14 : (valid_string output )) (PreH15 : (valid_string rev_output )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (problem_161_spec_z input rev_output )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p (n + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_entail_wit_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (retval = (string_length (input))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output 0 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full retval_2 0 output )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
) \/
(
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (flip_scan_state_z_161 input (@nil Z) 0 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
).

Definition solve_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (flip_scan_state_z_161 input (@nil Z) 0 0 ) ”
.

Definition solve_entail_wit_1_split_goal_2 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (0 <= retval) ”
.

Definition solve_entail_wit_1_split_goal_spatial := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (input)))) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : (problem_161_pre_z input )) (PreH7 : (ascii_range_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  (CharArray.undef_full retval_2 (retval + 1 ) )
.

Definition solve_entail_wit_2_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) > 122)) (PreH3 : ((Znth i (c_string (input)) 0) >= 97)) (PreH4 : ((Znth i (c_string (input)) 0) > 90)) (PreH5 : ((Znth i (c_string (input)) 0) >= 65)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (out <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= nletter)) (PreH12 : (nletter <= i)) (PreH13 : (0 <= w)) (PreH14 : (w <= 127)) (PreH15 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH16 : (valid_string input )) (PreH17 : (problem_161_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons ((signed_last_nbits ((Znth i (c_string (input)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (nletter + 1 )) ” 
  &&  “ ((nletter + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output (i + 1 ) (nletter + 1 ) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) > 122)) (PreH3 : ((Znth i (c_string (input)) 0) >= 97)) (PreH4 : ((Znth i (c_string (input)) 0) > 90)) (PreH5 : ((Znth i (c_string (input)) 0) >= 65)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (out <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= nletter)) (PreH12 : (nletter <= i)) (PreH13 : (0 <= w)) (PreH14 : (w <= 127)) (PreH15 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH16 : (valid_string input )) (PreH17 : (problem_161_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons ((signed_last_nbits ((Znth i (c_string (input)) 0)) (8))) ((@nil Z))))) (i + 1 ) (nletter + 1 ) ) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 127) ”
  &&  emp
).

Definition solve_entail_wit_2_1_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) > 122)) (PreH3 : ((Znth i (c_string (input)) 0) >= 97)) (PreH4 : ((Znth i (c_string (input)) 0) > 90)) (PreH5 : ((Znth i (c_string (input)) 0) >= 65)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (out <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= nletter)) (PreH12 : (nletter <= i)) (PreH13 : (0 <= w)) (PreH14 : (w <= 127)) (PreH15 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH16 : (valid_string input )) (PreH17 : (problem_161_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons ((signed_last_nbits ((Znth i (c_string (input)) 0)) (8))) ((@nil Z))))) (i + 1 ) (nletter + 1 ) ) ”
.

Definition solve_entail_wit_2_1_split_goal_2 := 
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) > 122)) (PreH3 : ((Znth i (c_string (input)) 0) >= 97)) (PreH4 : ((Znth i (c_string (input)) 0) > 90)) (PreH5 : ((Znth i (c_string (input)) 0) >= 65)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (out <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= nletter)) (PreH12 : (nletter <= i)) (PreH13 : (0 <= w)) (PreH14 : (w <= 127)) (PreH15 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH16 : (valid_string input )) (PreH17 : (problem_161_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth i (c_string (input)) 0) <= 127) ”
.

Definition solve_entail_wit_2_2 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 97)) (PreH3 : ((Znth i (c_string (input)) 0) < 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons ((signed_last_nbits ((Znth i (c_string (input)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (nletter + 1 )) ” 
  &&  “ ((nletter + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output (i + 1 ) (nletter + 1 ) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 97)) (PreH3 : ((Znth i (c_string (input)) 0) < 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons ((signed_last_nbits ((Znth i (c_string (input)) 0)) (8))) ((@nil Z))))) (i + 1 ) (nletter + 1 ) ) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ”
  &&  emp
).

Definition solve_entail_wit_2_2_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 97)) (PreH3 : ((Znth i (c_string (input)) 0) < 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons ((signed_last_nbits ((Znth i (c_string (input)) 0)) (8))) ((@nil Z))))) (i + 1 ) (nletter + 1 ) ) ”
.

Definition solve_entail_wit_2_2_split_goal_2 := 
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 97)) (PreH3 : ((Znth i (c_string (input)) 0) < 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (Znth i (c_string (input)) 0)) ”
.

Definition solve_entail_wit_2_3 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (nletter + 1 )) ” 
  &&  “ ((nletter + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output (i + 1 ) (nletter + 1 ) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) (nletter + 1 ) ) ”
  &&  emp
).

Definition solve_entail_wit_2_3_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons ((Znth i (c_string (input)) 0)) ((@nil Z))))) (i + 1 ) (nletter + 1 ) ) ”
.

Definition solve_entail_wit_2_4 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 122)) (PreH3 : ((Znth i (c_string (input)) 0) >= 97)) (PreH4 : ((Znth i (c_string (input)) 0) > 90)) (PreH5 : ((Znth i (c_string (input)) 0) >= 65)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (out <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= nletter)) (PreH12 : (nletter <= i)) (PreH13 : (0 <= w)) (PreH14 : (w <= 127)) (PreH15 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH16 : (valid_string input )) (PreH17 : (problem_161_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons (((Znth i (c_string (input)) 0) - 32 )) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= (i + 1 )) ” 
  &&  “ (0 <= ((Znth i (c_string (input)) 0) - 32 )) ” 
  &&  “ (((Znth i (c_string (input)) 0) - 32 ) <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output (i + 1 ) nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 122)) (PreH3 : ((Znth i (c_string (input)) 0) >= 97)) (PreH4 : ((Znth i (c_string (input)) 0) > 90)) (PreH5 : ((Znth i (c_string (input)) 0) >= 65)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (out <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= nletter)) (PreH12 : (nletter <= i)) (PreH13 : (0 <= w)) (PreH14 : (w <= 127)) (PreH15 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH16 : (valid_string input )) (PreH17 : (problem_161_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons (((Znth i (c_string (input)) 0) - 32 )) ((@nil Z))))) (i + 1 ) nletter ) ”
  &&  emp
).

Definition solve_entail_wit_2_4_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 122)) (PreH3 : ((Znth i (c_string (input)) 0) >= 97)) (PreH4 : ((Znth i (c_string (input)) 0) > 90)) (PreH5 : ((Znth i (c_string (input)) 0) >= 65)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (out <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (0 <= nletter)) (PreH12 : (nletter <= i)) (PreH13 : (0 <= w)) (PreH14 : (w <= 127)) (PreH15 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH16 : (valid_string input )) (PreH17 : (problem_161_pre_z input )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons (((Znth i (c_string (input)) 0) - 32 )) ((@nil Z))))) (i + 1 ) nletter ) ”
.

Definition solve_entail_wit_2_5 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (i + 1 ) (app (output_2) ((cons (((Znth i (c_string (input)) 0) + 32 )) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= (i + 1 )) ” 
  &&  “ (0 <= ((Znth i (c_string (input)) 0) + 32 )) ” 
  &&  “ (((Znth i (c_string (input)) 0) + 32 ) <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output (i + 1 ) nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons (((Znth i (c_string (input)) 0) + 32 )) ((@nil Z))))) (i + 1 ) nletter ) ”
  &&  emp
).

Definition solve_entail_wit_2_5_split_goal_1 := 
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (flip_scan_state_z_161 input (app (output_2) ((cons (((Znth i (c_string (input)) 0) + 32 )) ((@nil Z))))) (i + 1 ) nletter ) ”
.

Definition solve_entail_wit_3 := 
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (n: Z) (out: Z) (i: Z) (nletter: Z) (w: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (out <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= nletter)) (PreH6 : (nletter <= (i + 1 ))) (PreH7 : (0 <= w)) (PreH8 : (w <= 127)) (PreH9 : (flip_scan_state_z_161 input output_2 (i + 1 ) nletter )) (PreH10 : (valid_string input )) (PreH11 : (problem_161_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output_2 )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= (i + 1 )) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output (i + 1 ) nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (i + 1 ) output )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
.

Definition solve_entail_wit_4 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (out <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= nletter)) (PreH7 : (nletter <= i)) (PreH8 : (0 <= w)) (PreH9 : (w <= 127)) (PreH10 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH11 : (valid_string input )) (PreH12 : (problem_161_pre_z input )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out i output_2 )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= n) ” 
  &&  “ (flip_scan_state_z_161 input output n nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out n output )
  **  (CharArray.undef_seg out n (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (out <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= nletter)) (PreH8 : (nletter <= i)) (PreH9 : (0 <= w)) (PreH10 : (w <= 127)) (PreH11 : (flip_scan_state_z_161 input output_2 i nletter )) (PreH12 : (valid_string input )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out i output_2 )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= n) ” 
  &&  “ (flip_scan_state_z_161 input output n nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full out n output )
).

Definition solve_entail_wit_5 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (nletter = n)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (out <> 0)) (PreH7 : (0 <= nletter)) (PreH8 : (nletter <= n)) (PreH9 : (flip_scan_state_z_161 input output_2 n nletter )) (PreH10 : (valid_string input )) (PreH11 : (problem_161_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (n + 1 ) (app (output_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (n + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (nletter = n)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (out <> 0)) (PreH7 : (0 <= nletter)) (PreH8 : (nletter <= n)) (PreH9 : (flip_scan_state_z_161 input output_2 n nletter )) (PreH10 : (valid_string input )) (PreH11 : (problem_161_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  EX (output: (@list Z)) ,
  “ ((app (output_2) ((cons (0) ((@nil Z))))) = (c_string (output))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  emp
).

Definition solve_entail_wit_6 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (i = n)) (PreH7 : (out <> 0)) (PreH8 : (nletter = n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output_2 )) (PreH11 : (valid_string input )) (PreH12 : (valid_string output_2 )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (n + 1 ) (c_string (output_2)) )
|--
  EX (rev_output: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_scan_state_z_161 input rev_output 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full retval 0 rev_output )
  **  (CharArray.undef_seg retval 0 (n + 1 ) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (i = n)) (PreH7 : (out <> 0)) (PreH8 : (nletter = n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output_2 )) (PreH11 : (valid_string input )) (PreH12 : (valid_string output_2 )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  EX (output: (@list Z)) ,
  “ ((c_string (output_2)) = (c_string (output))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_scan_state_z_161 input (@nil Z) 0 ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.undef_full retval (n + 1 ) )
).

Definition solve_entail_wit_7 := 
(
forall (s_pre: Z) (input: (@list Z)) (rev_output_2: (@list Z)) (output_2: (@list Z)) (j: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (j < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (out <> 0)) (PreH7 : (p <> 0)) (PreH8 : (nletter = n)) (PreH9 : (0 <= j)) (PreH10 : (j <= n)) (PreH11 : (no_letter_z_161 input )) (PreH12 : (flip_output_z_161 input output_2 )) (PreH13 : (reverse_scan_state_z_161 input rev_output_2 j )) (PreH14 : (valid_string input )) (PreH15 : (valid_string output_2 )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (j + 1 ) (app (rev_output_2) ((cons ((Znth ((n - 1 ) - j ) (c_string (input)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg p (j + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (n + 1 ) (c_string (output_2)) )
|--
  EX (rev_output: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_scan_state_z_161 input rev_output (j + 1 ) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p (j + 1 ) rev_output )
  **  (CharArray.undef_seg p (j + 1 ) (n + 1 ) )
) \/
(
forall (input: (@list Z)) (rev_output_2: (@list Z)) (output_2: (@list Z)) (j: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (j < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (out <> 0)) (PreH7 : (p <> 0)) (PreH8 : (nletter = n)) (PreH9 : (0 <= j)) (PreH10 : (j <= n)) (PreH11 : (no_letter_z_161 input )) (PreH12 : (flip_output_z_161 input output_2 )) (PreH13 : (reverse_scan_state_z_161 input rev_output_2 j )) (PreH14 : (valid_string input )) (PreH15 : (valid_string output_2 )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  EX (output: (@list Z)) ,
  “ ((c_string (output_2)) = (c_string (output))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_scan_state_z_161 input (app (rev_output_2) ((cons ((Znth ((n - 1 ) - j ) (c_string (input)) 0)) ((@nil Z))))) (j + 1 ) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  emp
).

Definition solve_entail_wit_8 := 
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (rev_output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (p: Z) (nletter: Z) (j: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (p <> 0)) (PreH5 : (nletter = n)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (no_letter_z_161 input )) (PreH9 : (flip_output_z_161 input output_2 )) (PreH10 : (reverse_scan_state_z_161 input rev_output_2 (j + 1 ) )) (PreH11 : (valid_string input )) (PreH12 : (valid_string output_2 )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (ascii_range_z input )) (PreH15 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output_2)) )
  **  (CharArray.full p (j + 1 ) rev_output_2 )
  **  (CharArray.undef_seg p (j + 1 ) (n + 1 ) )
|--
  EX (rev_output: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_scan_state_z_161 input rev_output (j + 1 ) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p (j + 1 ) rev_output )
  **  (CharArray.undef_seg p (j + 1 ) (n + 1 ) )
.

Definition solve_entail_wit_9 := 
(
forall (s_pre: Z) (input: (@list Z)) (rev_output_2: (@list Z)) (output_2: (@list Z)) (j: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (j >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (i = n)) (PreH4 : (out <> 0)) (PreH5 : (p <> 0)) (PreH6 : (nletter = n)) (PreH7 : (0 <= j)) (PreH8 : (j <= n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output_2 )) (PreH11 : (reverse_scan_state_z_161 input rev_output_2 j )) (PreH12 : (valid_string input )) (PreH13 : (valid_string output_2 )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output_2)) )
  **  (CharArray.full p j rev_output_2 )
  **  (CharArray.undef_seg p j (n + 1 ) )
|--
  EX (rev_output: (@list Z))  (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (j = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_output_z_161 input rev_output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (valid_string rev_output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (problem_161_spec_z input rev_output ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p n rev_output )
  **  (CharArray.undef_seg p n (n + 1 ) )
) \/
(
forall (input: (@list Z)) (rev_output_2: (@list Z)) (output_2: (@list Z)) (j: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (j >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (i = n)) (PreH5 : (out <> 0)) (PreH6 : (p <> 0)) (PreH7 : (nletter = n)) (PreH8 : (0 <= j)) (PreH9 : (j <= n)) (PreH10 : (no_letter_z_161 input )) (PreH11 : (flip_output_z_161 input output_2 )) (PreH12 : (reverse_scan_state_z_161 input rev_output_2 j )) (PreH13 : (valid_string input )) (PreH14 : (valid_string output_2 )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p j rev_output_2 )
|--
  EX (rev_output: (@list Z))  (output: (@list Z)) ,
  “ ((c_string (output_2)) = (c_string (output))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (j = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_output_z_161 input rev_output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (valid_string rev_output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (problem_161_spec_z input rev_output ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full p n rev_output )
).

Definition solve_entail_wit_10 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (nletter <> n)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (out <> 0)) (PreH7 : (0 <= nletter)) (PreH8 : (nletter <= n)) (PreH9 : (flip_scan_state_z_161 input output_2 n nletter )) (PreH10 : (valid_string input )) (PreH11 : (problem_161_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (n + 1 ) (app (output_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (n + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (nletter <> n) ” 
  &&  “ (has_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (problem_161_spec_z input output ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (nletter <> n)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (0 <= n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (out <> 0)) (PreH7 : (0 <= nletter)) (PreH8 : (nletter <= n)) (PreH9 : (flip_scan_state_z_161 input output_2 n nletter )) (PreH10 : (valid_string input )) (PreH11 : (problem_161_pre_z input )) (PreH12 : (ascii_range_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  EX (output: (@list Z)) ,
  “ ((app (output_2) ((cons (0) ((@nil Z))))) = (c_string (output))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (nletter <> n) ” 
  &&  “ (has_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (problem_161_spec_z input output ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  emp
).

Definition solve_return_wit_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (nletter <> n)) (PreH5 : (has_letter_z_161 input )) (PreH6 : (flip_output_z_161 input output_2 )) (PreH7 : (valid_string input )) (PreH8 : (valid_string output_2 )) (PreH9 : (problem_161_pre_z input )) (PreH10 : (problem_161_spec_z input output_2 )) (PreH11 : (ascii_range_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output_2)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_161_spec_z input output ) ” 
  &&  “ (valid_string output ) ”
  &&  (store_string s_pre input )
  **  (store_string out output )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (i = n)) (PreH5 : (out <> 0)) (PreH6 : (nletter <> n)) (PreH7 : (has_letter_z_161 input )) (PreH8 : (flip_output_z_161 input output_2 )) (PreH9 : (valid_string input )) (PreH10 : (valid_string output_2 )) (PreH11 : (problem_161_pre_z input )) (PreH12 : (problem_161_spec_z input output_2 )) (PreH13 : (ascii_range_z input )) (PreH14 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full out (n + 1 ) (c_string (output_2)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_161_spec_z input output ) ” 
  &&  “ (valid_string output ) ”
  &&  (CharArray.full out ((string_length (output)) + 1 ) (c_string (output)) )
).

Definition solve_return_wit_2 := 
(
forall (s_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= n)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (j = n)) (PreH7 : (out <> 0)) (PreH8 : (p <> 0)) (PreH9 : (nletter = n)) (PreH10 : (no_letter_z_161 input )) (PreH11 : (flip_output_z_161 input output_2 )) (PreH12 : (reverse_output_z_161 input rev_output )) (PreH13 : (valid_string input )) (PreH14 : (valid_string output_2 )) (PreH15 : (valid_string rev_output )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (problem_161_spec_z input rev_output )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output: (@list Z)) ,
  “ (problem_161_spec_z input output ) ” 
  &&  “ (valid_string output ) ”
  &&  (store_string s_pre input )
  **  (store_string p output )
) \/
(
forall (input: (@list Z)) (output_2: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= n)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (j = n)) (PreH7 : (out <> 0)) (PreH8 : (p <> 0)) (PreH9 : (nletter = n)) (PreH10 : (no_letter_z_161 input )) (PreH11 : (flip_output_z_161 input output_2 )) (PreH12 : (reverse_output_z_161 input rev_output )) (PreH13 : (valid_string input )) (PreH14 : (valid_string output_2 )) (PreH15 : (valid_string rev_output )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (problem_161_spec_z input rev_output )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
|--
  EX (output: (@list Z)) ,
  “ (problem_161_spec_z input output ) ” 
  &&  “ (valid_string output ) ”
  &&  (CharArray.full p ((string_length (output)) + 1 ) (c_string (output)) )
).

Definition solve_partial_solve_wit_1_pure := 
forall (s_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_161_pre_z input )) (PreH3 : (ascii_range_z input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition solve_partial_solve_wit_1_aux := 
forall (s_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_161_pre_z input )) (PreH3 : (ascii_range_z input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string s_pre input )
.

Definition solve_partial_solve_wit_1 := solve_partial_solve_wit_1_pure -> solve_partial_solve_wit_1_aux.

Definition solve_partial_solve_wit_2_pure := 
(
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_161_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (retval = (string_length (input)))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (valid_string input )) (PreH8 : (problem_161_pre_z input )) (PreH9 : (ascii_range_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition solve_partial_solve_wit_2_pure_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (retval = (string_length (input)))) (PreH6 : (0 <= ((string_length (input)) + 1 ))) (PreH7 : (valid_string input )) (PreH8 : (problem_161_pre_z input )) (PreH9 : (ascii_range_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "nletter" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition solve_partial_solve_wit_2_aux := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_161_pre_z input )) (PreH5 : (ascii_range_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition solve_partial_solve_wit_2 := solve_partial_solve_wit_2_pure -> solve_partial_solve_wit_2_aux.

Definition solve_partial_solve_wit_3 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 90) ” 
  &&  “ ((Znth i (c_string (input)) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= i) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output i nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i output )
.

Definition solve_partial_solve_wit_4 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 122)) (PreH2 : ((Znth i (c_string (input)) 0) >= 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) <= 122) ” 
  &&  “ ((Znth i (c_string (input)) 0) >= 97) ” 
  &&  “ ((Znth i (c_string (input)) 0) > 90) ” 
  &&  “ ((Znth i (c_string (input)) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= i) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output i nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i output )
.

Definition solve_partial_solve_wit_5 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 97)) (PreH2 : ((Znth i (c_string (input)) 0) > 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (out <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= nletter)) (PreH10 : (nletter <= i)) (PreH11 : (0 <= w)) (PreH12 : (w <= 127)) (PreH13 : (flip_scan_state_z_161 input output i nletter )) (PreH14 : (valid_string input )) (PreH15 : (problem_161_pre_z input )) (PreH16 : (ascii_range_z input )) (PreH17 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) < 97) ” 
  &&  “ ((Znth i (c_string (input)) 0) > 90) ” 
  &&  “ ((Znth i (c_string (input)) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= i) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output i nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i output )
.

Definition solve_partial_solve_wit_6 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 97)) (PreH2 : ((Znth i (c_string (input)) 0) < 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (out <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= nletter)) (PreH9 : (nletter <= i)) (PreH10 : (0 <= w)) (PreH11 : (w <= 127)) (PreH12 : (flip_scan_state_z_161 input output i nletter )) (PreH13 : (valid_string input )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) < 97) ” 
  &&  “ ((Znth i (c_string (input)) 0) < 65) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= i) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output i nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i output )
.

Definition solve_partial_solve_wit_7 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (w: Z) (nletter: Z) (i: Z) (out: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) > 122)) (PreH2 : ((Znth i (c_string (input)) 0) >= 97)) (PreH3 : ((Znth i (c_string (input)) 0) > 90)) (PreH4 : ((Znth i (c_string (input)) 0) >= 65)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (out <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= nletter)) (PreH11 : (nletter <= i)) (PreH12 : (0 <= w)) (PreH13 : (w <= 127)) (PreH14 : (flip_scan_state_z_161 input output i nletter )) (PreH15 : (valid_string input )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (ascii_range_z input )) (PreH18 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out i output )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) > 122) ” 
  &&  “ ((Znth i (c_string (input)) 0) >= 97) ” 
  &&  “ ((Znth i (c_string (input)) 0) > 90) ” 
  &&  “ ((Znth i (c_string (input)) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= i) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= 127) ” 
  &&  “ (flip_scan_state_z_161 input output i nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i output )
.

Definition solve_partial_solve_wit_8 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (0 <= nletter)) (PreH5 : (nletter <= n)) (PreH6 : (flip_scan_state_z_161 input output n nletter )) (PreH7 : (valid_string input )) (PreH8 : (problem_161_pre_z input )) (PreH9 : (ascii_range_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out n output )
  **  (CharArray.undef_seg out n (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= nletter) ” 
  &&  “ (nletter <= n) ” 
  &&  “ (flip_scan_state_z_161 input output n nletter ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((out + (n * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i out n n (n + 1 ) )
  **  (CharArray.full out n output )
.

Definition solve_partial_solve_wit_9_pure := 
(
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (nletter = n)) (PreH5 : (no_letter_z_161 input )) (PreH6 : (flip_output_z_161 input output )) (PreH7 : (valid_string input )) (PreH8 : (valid_string output )) (PreH9 : (problem_161_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((n + 1 ) > 0) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (PreH1 : (w <= INT_MAX)) (PreH2 : (nletter <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (w >= INT_MIN)) (PreH6 : (nletter >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (0 <= ((string_length (input)) + 1 ))) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (n = (string_length (input)))) (PreH12 : (i = n)) (PreH13 : (out <> 0)) (PreH14 : (nletter = n)) (PreH15 : (no_letter_z_161 input )) (PreH16 : (flip_output_z_161 input output )) (PreH17 : (valid_string input )) (PreH18 : (valid_string output )) (PreH19 : (problem_161_pre_z input )) (PreH20 : (ascii_range_z input )) (PreH21 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((n + 1 ) > 0) ”
).

Definition solve_partial_solve_wit_9_pure_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (w: Z) (PreH1 : (w <= INT_MAX)) (PreH2 : (nletter <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (w >= INT_MIN)) (PreH6 : (nletter >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (0 <= ((string_length (input)) + 1 ))) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (n = (string_length (input)))) (PreH12 : (i = n)) (PreH13 : (out <> 0)) (PreH14 : (nletter = n)) (PreH15 : (no_letter_z_161 input )) (PreH16 : (flip_output_z_161 input output )) (PreH17 : (valid_string input )) (PreH18 : (valid_string output )) (PreH19 : (problem_161_pre_z input )) (PreH20 : (ascii_range_z input )) (PreH21 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((n + 1 ) > 0) ”
.

Definition solve_partial_solve_wit_9_aux := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (n: Z) (i: Z) (out: Z) (nletter: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (out <> 0)) (PreH4 : (nletter = n)) (PreH5 : (no_letter_z_161 input )) (PreH6 : (flip_output_z_161 input output )) (PreH7 : (valid_string input )) (PreH8 : (valid_string output )) (PreH9 : (problem_161_pre_z input )) (PreH10 : (ascii_range_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((n + 1 ) > 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
.

Definition solve_partial_solve_wit_9 := solve_partial_solve_wit_9_pure -> solve_partial_solve_wit_9_aux.

Definition solve_partial_solve_wit_10 := 
forall (s_pre: Z) (input: (@list Z)) (rev_output: (@list Z)) (output: (@list Z)) (j: Z) (nletter: Z) (p: Z) (out: Z) (i: Z) (n: Z) (PreH1 : (j < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (i = n)) (PreH4 : (out <> 0)) (PreH5 : (p <> 0)) (PreH6 : (nletter = n)) (PreH7 : (0 <= j)) (PreH8 : (j <= n)) (PreH9 : (no_letter_z_161 input )) (PreH10 : (flip_output_z_161 input output )) (PreH11 : (reverse_scan_state_z_161 input rev_output j )) (PreH12 : (valid_string input )) (PreH13 : (valid_string output )) (PreH14 : (problem_161_pre_z input )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p j rev_output )
  **  (CharArray.undef_seg p j (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_scan_state_z_161 input rev_output j ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((p + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i p j j (n + 1 ) )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p j rev_output )
.

Definition solve_partial_solve_wit_11 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (i = n)) (PreH3 : (j = n)) (PreH4 : (out <> 0)) (PreH5 : (p <> 0)) (PreH6 : (nletter = n)) (PreH7 : (no_letter_z_161 input )) (PreH8 : (flip_output_z_161 input output )) (PreH9 : (reverse_output_z_161 input rev_output )) (PreH10 : (valid_string input )) (PreH11 : (valid_string output )) (PreH12 : (valid_string rev_output )) (PreH13 : (problem_161_pre_z input )) (PreH14 : (problem_161_spec_z input rev_output )) (PreH15 : (ascii_range_z input )) (PreH16 : ((string_length (input)) < INT_MAX)) ,
  (store_string s_pre input )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p n rev_output )
  **  (CharArray.undef_seg p n (n + 1 ) )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (j = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_output_z_161 input rev_output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (valid_string rev_output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (problem_161_spec_z input rev_output ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (((p + (n * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.undef_missing_i p n n (n + 1 ) )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p n rev_output )
.

Definition solve_partial_solve_wit_12_pure := 
(
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (w: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= n)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (j = n)) (PreH7 : (out <> 0)) (PreH8 : (p <> 0)) (PreH9 : (nletter = n)) (PreH10 : (no_letter_z_161 input )) (PreH11 : (flip_output_z_161 input output )) (PreH12 : (reverse_output_z_161 input rev_output )) (PreH13 : (valid_string input )) (PreH14 : (valid_string output )) (PreH15 : (valid_string rev_output )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (problem_161_spec_z input rev_output )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p (n + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ (out <> 0) ” 
  &&  “ (0 < (n + 1 )) ” 
  &&  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((Zlength ((c_string (output)))) = (n + 1 )) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (w: Z) (PreH1 : (w <= INT_MAX)) (PreH2 : (nletter <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (w >= INT_MIN)) (PreH7 : (nletter >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (0 <= ((string_length (input)) + 1 ))) (PreH12 : (0 <= n)) (PreH13 : (0 <= (n + 1 ))) (PreH14 : (n = (string_length (input)))) (PreH15 : (i = n)) (PreH16 : (j = n)) (PreH17 : (out <> 0)) (PreH18 : (p <> 0)) (PreH19 : (nletter = n)) (PreH20 : (no_letter_z_161 input )) (PreH21 : (flip_output_z_161 input output )) (PreH22 : (reverse_output_z_161 input rev_output )) (PreH23 : (valid_string input )) (PreH24 : (valid_string output )) (PreH25 : (valid_string rev_output )) (PreH26 : (problem_161_pre_z input )) (PreH27 : (problem_161_spec_z input rev_output )) (PreH28 : (ascii_range_z input )) (PreH29 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((Zlength ((c_string (output)))) = (n + 1 )) ”
).

Definition solve_partial_solve_wit_12_pure_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (w: Z) (PreH1 : (w <= INT_MAX)) (PreH2 : (nletter <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (w >= INT_MIN)) (PreH7 : (nletter >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (0 <= ((string_length (input)) + 1 ))) (PreH12 : (0 <= n)) (PreH13 : (0 <= (n + 1 ))) (PreH14 : (n = (string_length (input)))) (PreH15 : (i = n)) (PreH16 : (j = n)) (PreH17 : (out <> 0)) (PreH18 : (p <> 0)) (PreH19 : (nletter = n)) (PreH20 : (no_letter_z_161 input )) (PreH21 : (flip_output_z_161 input output )) (PreH22 : (reverse_output_z_161 input rev_output )) (PreH23 : (valid_string input )) (PreH24 : (valid_string output )) (PreH25 : (valid_string rev_output )) (PreH26 : (problem_161_pre_z input )) (PreH27 : (problem_161_spec_z input rev_output )) (PreH28 : (ascii_range_z input )) (PreH29 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "nletter" ) )) # Int  |-> nletter)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ ((Zlength ((c_string (output)))) = (n + 1 )) ”
.

Definition solve_partial_solve_wit_12_aux := 
forall (s_pre: Z) (input: (@list Z)) (output: (@list Z)) (rev_output: (@list Z)) (n: Z) (i: Z) (j: Z) (out: Z) (p: Z) (nletter: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= n)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (i = n)) (PreH6 : (j = n)) (PreH7 : (out <> 0)) (PreH8 : (p <> 0)) (PreH9 : (nletter = n)) (PreH10 : (no_letter_z_161 input )) (PreH11 : (flip_output_z_161 input output )) (PreH12 : (reverse_output_z_161 input rev_output )) (PreH13 : (valid_string input )) (PreH14 : (valid_string output )) (PreH15 : (valid_string rev_output )) (PreH16 : (problem_161_pre_z input )) (PreH17 : (problem_161_spec_z input rev_output )) (PreH18 : (ascii_range_z input )) (PreH19 : ((string_length (input)) < INT_MAX)) ,
  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p (n + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full out (n + 1 ) (c_string (output)) )
|--
  “ (out <> 0) ” 
  &&  “ (0 < (n + 1 )) ” 
  &&  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((Zlength ((c_string (output)))) = (n + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (i = n) ” 
  &&  “ (j = n) ” 
  &&  “ (out <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (nletter = n) ” 
  &&  “ (no_letter_z_161 input ) ” 
  &&  “ (flip_output_z_161 input output ) ” 
  &&  “ (reverse_output_z_161 input rev_output ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (valid_string output ) ” 
  &&  “ (valid_string rev_output ) ” 
  &&  “ (problem_161_pre_z input ) ” 
  &&  “ (problem_161_spec_z input rev_output ) ” 
  &&  “ (ascii_range_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (CharArray.full out (n + 1 ) (c_string (output)) )
  **  (CharArray.full p (n + 1 ) (app (rev_output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition solve_partial_solve_wit_12 := solve_partial_solve_wit_12_pure -> solve_partial_solve_wit_12_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_solve_safety_wit_1 : solve_safety_wit_1.
Axiom proof_of_solve_safety_wit_2 : solve_safety_wit_2.
Axiom proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Axiom proof_of_solve_safety_wit_4 : solve_safety_wit_4.
Axiom proof_of_solve_safety_wit_5 : solve_safety_wit_5.
Axiom proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Axiom proof_of_solve_safety_wit_7 : solve_safety_wit_7.
Axiom proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Axiom proof_of_solve_safety_wit_9 : solve_safety_wit_9.
Axiom proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Axiom proof_of_solve_safety_wit_11 : solve_safety_wit_11.
Axiom proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Axiom proof_of_solve_safety_wit_13 : solve_safety_wit_13.
Axiom proof_of_solve_safety_wit_14 : solve_safety_wit_14.
Axiom proof_of_solve_safety_wit_15 : solve_safety_wit_15.
Axiom proof_of_solve_safety_wit_16 : solve_safety_wit_16.
Axiom proof_of_solve_safety_wit_17 : solve_safety_wit_17.
Axiom proof_of_solve_safety_wit_18 : solve_safety_wit_18.
Axiom proof_of_solve_safety_wit_19 : solve_safety_wit_19.
Axiom proof_of_solve_safety_wit_20 : solve_safety_wit_20.
Axiom proof_of_solve_safety_wit_21 : solve_safety_wit_21.
Axiom proof_of_solve_safety_wit_22 : solve_safety_wit_22.
Axiom proof_of_solve_safety_wit_23 : solve_safety_wit_23.
Axiom proof_of_solve_safety_wit_24 : solve_safety_wit_24.
Axiom proof_of_solve_safety_wit_25 : solve_safety_wit_25.
Axiom proof_of_solve_safety_wit_26 : solve_safety_wit_26.
Axiom proof_of_solve_safety_wit_27 : solve_safety_wit_27.
Axiom proof_of_solve_safety_wit_28 : solve_safety_wit_28.
Axiom proof_of_solve_safety_wit_29 : solve_safety_wit_29.
Axiom proof_of_solve_safety_wit_30 : solve_safety_wit_30.
Axiom proof_of_solve_safety_wit_31 : solve_safety_wit_31.
Axiom proof_of_solve_safety_wit_32 : solve_safety_wit_32.
Axiom proof_of_solve_safety_wit_33 : solve_safety_wit_33.
Axiom proof_of_solve_safety_wit_34 : solve_safety_wit_34.
Axiom proof_of_solve_safety_wit_35 : solve_safety_wit_35.
Axiom proof_of_solve_safety_wit_36 : solve_safety_wit_36.
Axiom proof_of_solve_safety_wit_37 : solve_safety_wit_37.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2_1 : solve_entail_wit_2_1.
Axiom proof_of_solve_entail_wit_2_2 : solve_entail_wit_2_2.
Axiom proof_of_solve_entail_wit_2_3 : solve_entail_wit_2_3.
Axiom proof_of_solve_entail_wit_2_4 : solve_entail_wit_2_4.
Axiom proof_of_solve_entail_wit_2_5 : solve_entail_wit_2_5.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Axiom proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Axiom proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Axiom proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Axiom proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_return_wit_2 : solve_return_wit_2.
Axiom proof_of_solve_partial_solve_wit_1_pure : solve_partial_solve_wit_1_pure.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.
Axiom proof_of_solve_partial_solve_wit_2_pure : solve_partial_solve_wit_2_pure.
Axiom proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2.
Axiom proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3.
Axiom proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4.
Axiom proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5.
Axiom proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6.
Axiom proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7.
Axiom proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8.
Axiom proof_of_solve_partial_solve_wit_9_pure : solve_partial_solve_wit_9_pure.
Axiom proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9.
Axiom proof_of_solve_partial_solve_wit_10 : solve_partial_solve_wit_10.
Axiom proof_of_solve_partial_solve_wit_11 : solve_partial_solve_wit_11.
Axiom proof_of_solve_partial_solve_wit_12_pure : solve_partial_solve_wit_12_pure.
Axiom proof_of_solve_partial_solve_wit_12 : solve_partial_solve_wit_12.

End VC_Correct.
