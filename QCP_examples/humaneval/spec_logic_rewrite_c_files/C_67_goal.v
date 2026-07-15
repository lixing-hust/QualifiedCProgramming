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
Require Import coins_67.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function fruit_distribution -----*)

Definition fruit_distribution_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "num1" ) )) # Int  |->_)
  **  (store_string s_pre str_l )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "num1" ) )) # Int  |->_)
  **  (store_string s_pre str_l )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "num2" ) )) # Int  |->_)
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  (store_string s_pre str_l )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_4 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "num2" ) )) # Int  |->_)
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  (store_string s_pre str_l )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_5 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "num2" ) )) # Int  |-> (-1))
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  (store_string s_pre str_l )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_6 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "num2" ) )) # Int  |-> (-1))
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  (store_string s_pre str_l )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_7 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
  **  ((( &( "num2" ) )) # Int  |-> (-1))
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  (store_string s_pre str_l )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_8 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (i < len)) (PreH2 : (0 <= i)) (PreH3 : (i <= len)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_67_pre_z str_l n_pre )) (PreH10 : (fruit_safe_input_67 str_l n_pre )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition fruit_distribution_safety_wit_9 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH2 : (i < len)) (PreH3 : (0 <= i)) (PreH4 : (i <= len)) (PreH5 : (len = (string_length (str_l)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (57 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 57) ”
.

Definition fruit_distribution_safety_wit_10 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH2 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH3 : (i < len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_11 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_12 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH10 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (is_digit_z_67 ch )) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH19 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cur * 10 ) + (ch - 48 ) )) ”
.

Definition fruit_distribution_safety_wit_13 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH10 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (is_digit_z_67 ch )) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH19 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ ((ch - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ch - 48 )) ”
.

Definition fruit_distribution_safety_wit_14 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH10 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (is_digit_z_67 ch )) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH19 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ ((cur * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur * 10 )) ”
.

Definition fruit_distribution_safety_wit_15 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH10 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (is_digit_z_67 ch )) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH19 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fruit_distribution_safety_wit_16 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH10 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (is_digit_z_67 ch )) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH19 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition fruit_distribution_safety_wit_17 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH2 : (i < len)) (PreH3 : (0 <= i)) (PreH4 : (i <= len)) (PreH5 : (len = (string_length (str_l)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_18 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH2 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH3 : (i < len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_19 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH3 : (i < len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_20 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_21 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_22 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_23 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_24 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_25 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 >= 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_26 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 >= 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_27 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_28 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_29 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_30 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_31 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_32 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_33 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_34 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_35 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (cur <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fruit_distribution_safety_wit_36 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= INT_MAX)) (PreH11 : (cur = (-1))) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (store_string s_pre str_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fruit_distribution_safety_wit_37 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= INT_MAX)) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= INT_MAX)) (PreH13 : (cur = (-1))) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (problem_67_pre_z str_l n_pre )) (PreH17 : (fruit_safe_input_67 str_l n_pre )) (PreH18 : ((string_length (str_l)) < INT_MAX)) (PreH19 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fruit_distribution_safety_wit_38 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= INT_MAX)) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= INT_MAX)) (PreH13 : (cur = (-1))) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (problem_67_pre_z str_l n_pre )) (PreH17 : (fruit_safe_input_67 str_l n_pre )) (PreH18 : ((string_length (str_l)) < INT_MAX)) (PreH19 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fruit_distribution_safety_wit_39 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (cur < 0)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fruit_distribution_safety_wit_40 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (i >= len)) (PreH2 : (0 <= i)) (PreH3 : (i <= len)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_67_pre_z str_l n_pre )) (PreH10 : (fruit_safe_input_67 str_l n_pre )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_41 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur >= 0)) (PreH2 : (i >= len)) (PreH3 : (0 <= i)) (PreH4 : (i <= len)) (PreH5 : (len = (string_length (str_l)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_42 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : (i >= len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_43 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : (i >= len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_44 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 >= 0)) (PreH2 : (cur >= 0)) (PreH3 : (i >= len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_45 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_46 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_47 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition fruit_distribution_safety_wit_48 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fruit_distribution_safety_wit_49 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= INT_MAX)) (PreH7 : (cur = (-1))) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_50 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= INT_MAX)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= INT_MAX)) (PreH9 : (cur = (-1))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_51 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= INT_MAX)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= INT_MAX)) (PreH9 : (cur = (-1))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_52 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur < 0)) (PreH2 : (i >= len)) (PreH3 : (0 <= i)) (PreH4 : (i <= len)) (PreH5 : (len = (string_length (str_l)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_53 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num1 < 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (cur = (-1))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (store_string s_pre str_l )
|--
  “ False ”
.

Definition fruit_distribution_safety_wit_54 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num1 < 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ False ”
.

Definition fruit_distribution_safety_wit_55 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num1 < 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ False ”
.

Definition fruit_distribution_safety_wit_56 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur < 0)) (PreH3 : (i >= len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_57 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (num1 = 0)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (problem_67_pre_z str_l n_pre )) (PreH9 : (fruit_safe_input_67 str_l n_pre )) (PreH10 : ((string_length (str_l)) < INT_MAX)) (PreH11 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_58 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num1 >= 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (cur = (-1))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_59 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num1 >= 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_60 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num1 >= 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (0 <= num2)) (PreH9 : (num2 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_61 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 >= 0)) (PreH2 : (cur < 0)) (PreH3 : (i >= len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_62 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 <= num1)) (PreH8 : (num1 <= INT_MAX)) (PreH9 : (0 <= num2)) (PreH10 : (num2 <= INT_MAX)) (PreH11 : (cur = (-1))) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ False ”
.

Definition fruit_distribution_safety_wit_63 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 <= num1)) (PreH8 : (num1 <= INT_MAX)) (PreH9 : (0 <= num2)) (PreH10 : (num2 <= INT_MAX)) (PreH11 : (cur = (-1))) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ False ”
.

Definition fruit_distribution_safety_wit_64 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num2 < 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (num1 = 0)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_67_pre_z str_l n_pre )) (PreH10 : (fruit_safe_input_67 str_l n_pre )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_65 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 <= num1)) (PreH8 : (num1 <= INT_MAX)) (PreH9 : (cur = (-1))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_66 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur < 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fruit_distribution_safety_wit_67 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= INT_MAX)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= INT_MAX)) (PreH9 : (0 <= ((n_pre - num1 ) - num2 ))) (PreH10 : (((n_pre - num1 ) - num2 ) <= INT_MAX)) (PreH11 : (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) )) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre - num1 ) - num2 )) ”
.

Definition fruit_distribution_safety_wit_68 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= INT_MAX)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= INT_MAX)) (PreH9 : (0 <= ((n_pre - num1 ) - num2 ))) (PreH10 : (((n_pre - num1 ) - num2 ) <= INT_MAX)) (PreH11 : (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) )) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (store_string s_pre str_l )
|--
  “ ((n_pre - num1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - num1 )) ”
.

Definition fruit_distribution_entail_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string s_pre str_l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre 0 (-1) (-1) (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre 0 (-1) (-1) (-1) ) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre 0 (-1) (-1) (-1) ) ”
.

Definition fruit_distribution_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (problem_67_pre_z str_l n_pre )) (PreH8 : (fruit_safe_input_67 str_l n_pre )) (PreH9 : ((string_length (str_l)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition fruit_distribution_entail_wit_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (48 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 57) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (is_digit_z_67 (Znth i (c_string (str_l)) 0) ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre i num1 num2 0 ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre i num1 num2 0 ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (is_digit_z_67 (Znth i (c_string (str_l)) 0) ) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre i num1 num2 0 ) ”
.

Definition fruit_distribution_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ”
.

Definition fruit_distribution_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (is_digit_z_67 (Znth i (c_string (str_l)) 0) ) ”
.

Definition fruit_distribution_entail_wit_3_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (48 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 57) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (0 <= ((cur * 10 ) + ((Znth i (c_string (str_l)) 0) - 48 ) )) ” 
  &&  “ (((cur * 10 ) + ((Znth i (c_string (str_l)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (is_digit_z_67 (Znth i (c_string (str_l)) 0) ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((digit_value_z_67 ((Znth i (c_string (str_l)) 0))) = ((Znth i (c_string (str_l)) 0) - 48 )) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre i num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((digit_value_z_67 ((Znth i (c_string (str_l)) 0))) = ((Znth i (c_string (str_l)) 0) - 48 )) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (is_digit_z_67 (Znth i (c_string (str_l)) 0) ) ” 
  &&  “ (((cur * 10 ) + ((Znth i (c_string (str_l)) 0) - 48 ) ) <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((digit_value_z_67 ((Znth i (c_string (str_l)) 0))) = ((Znth i (c_string (str_l)) 0) - 48 )) ”
.

Definition fruit_distribution_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ”
.

Definition fruit_distribution_entail_wit_3_1_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (is_digit_z_67 (Znth i (c_string (str_l)) 0) ) ”
.

Definition fruit_distribution_entail_wit_3_1_split_goal_4 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (((cur * 10 ) + ((Znth i (c_string (str_l)) 0) - 48 ) ) <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_3_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (cur = 0)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (is_digit_z_67 ch )) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (48 <= ch) ” 
  &&  “ (ch <= 57) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (0 <= ((cur * 10 ) + (ch - 48 ) )) ” 
  &&  “ (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (is_digit_z_67 ch ) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((digit_value_z_67 (ch)) = (ch - 48 )) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre i num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < len)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (48 <= ch)) (PreH8 : (ch <= 57)) (PreH9 : (cur = 0)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (is_digit_z_67 ch )) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((digit_value_z_67 (ch)) = (ch - 48 )) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < len)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (48 <= ch)) (PreH8 : (ch <= 57)) (PreH9 : (cur = 0)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (is_digit_z_67 ch )) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((digit_value_z_67 (ch)) = (ch - 48 )) ”
.

Definition fruit_distribution_entail_wit_4 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH10 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (is_digit_z_67 ch )) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH19 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (48 <= ch) ” 
  &&  “ (ch <= 57) ” 
  &&  “ (0 <= ((cur * 10 ) + (ch - 48 ) )) ” 
  &&  “ (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 ((cur * 10 ) + (ch - 48 ) ) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < len)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (48 <= ch)) (PreH8 : (ch <= 57)) (PreH9 : (0 <= cur)) (PreH10 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH11 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (is_digit_z_67 ch )) (PreH18 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH19 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH20 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 ((cur * 10 ) + (ch - 48 ) ) ) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < len)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (48 <= ch)) (PreH8 : (ch <= 57)) (PreH9 : (0 <= cur)) (PreH10 : (0 <= ((cur * 10 ) + (ch - 48 ) ))) (PreH11 : (((cur * 10 ) + (ch - 48 ) ) <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (is_digit_z_67 ch )) (PreH18 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH19 : ((digit_value_z_67 (ch)) = (ch - 48 ))) (PreH20 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 ((cur * 10 ) + (ch - 48 ) ) ) ”
.

Definition fruit_distribution_entail_wit_5_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) cur num2 (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) cur num2 (-1) ) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_5_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) cur num2 (-1) ) ”
.

Definition fruit_distribution_entail_wit_5_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (cur <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_5_1_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition fruit_distribution_entail_wit_5_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) cur num2 (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) cur num2 (-1) ) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_5_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) cur num2 (-1) ) ”
.

Definition fruit_distribution_entail_wit_5_2_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (cur <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_5_2_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition fruit_distribution_entail_wit_6_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 cur (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 cur (-1) ) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_6_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 cur (-1) ) ”
.

Definition fruit_distribution_entail_wit_6_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (cur <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_6_1_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_6_1_split_goal_4 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition fruit_distribution_entail_wit_6_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 cur (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 cur (-1) ) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_6_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 cur (-1) ) ”
.

Definition fruit_distribution_entail_wit_6_2_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (cur <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_6_2_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_6_2_split_goal_4 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition fruit_distribution_entail_wit_7_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH5 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 (-1) ) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_7_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 (-1) ) ”
.

Definition fruit_distribution_entail_wit_7_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num2 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_7_1_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_7_1_split_goal_4 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH6 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH7 : (i < len)) (PreH8 : (0 <= i)) (PreH9 : (i <= len)) (PreH10 : (len = (string_length (str_l)))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition fruit_distribution_entail_wit_7_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 (-1) ) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_7_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 (-1) ) ”
.

Definition fruit_distribution_entail_wit_7_2_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num2 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_7_2_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_7_2_split_goal_4 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH6 : (i < len)) (PreH7 : (0 <= i)) (PreH8 : (i <= len)) (PreH9 : (len = (string_length (str_l)))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition fruit_distribution_entail_wit_8_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (cur < 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_8_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
.

Definition fruit_distribution_entail_wit_8_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) > 57)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 48)) (PreH5 : (i < len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition fruit_distribution_entail_wit_8_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (cur < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH3 : (i < len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ ~(((48 <= (Znth i (c_string (str_l)) 0)) /\ ((Znth i (c_string (str_l)) 0) <= 57))) ” 
  &&  “ (cur < 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_8_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
.

Definition fruit_distribution_entail_wit_8_2_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (cur < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) < 48)) (PreH4 : (i < len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition fruit_distribution_entail_wit_9_1 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (48 <= ch)) (PreH7 : (ch <= 57)) (PreH8 : (0 <= cur)) (PreH9 : (cur <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
.

Definition fruit_distribution_entail_wit_9_2 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= INT_MAX)) (PreH11 : (cur = (-1))) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
.

Definition fruit_distribution_entail_wit_9_3 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= INT_MAX)) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= INT_MAX)) (PreH13 : (cur = (-1))) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (problem_67_pre_z str_l n_pre )) (PreH17 : (fruit_safe_input_67 str_l n_pre )) (PreH18 : ((string_length (str_l)) < INT_MAX)) (PreH19 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
.

Definition fruit_distribution_entail_wit_9_4 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (0 <= num1)) (PreH10 : (num1 <= INT_MAX)) (PreH11 : (0 <= num2)) (PreH12 : (num2 <= INT_MAX)) (PreH13 : (cur = (-1))) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (problem_67_pre_z str_l n_pre )) (PreH17 : (fruit_safe_input_67 str_l n_pre )) (PreH18 : ((string_length (str_l)) < INT_MAX)) (PreH19 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
.

Definition fruit_distribution_entail_wit_9_5 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (i: Z) (len: Z) (ch: Z) (cur: Z) (num2: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < len)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : ~(((48 <= ch) /\ (ch <= 57)))) (PreH9 : (cur < 0)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (len = (string_length (str_l))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre (i + 1 ) num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
.

Definition fruit_distribution_entail_wit_10 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur >= 0)) (PreH3 : (i >= len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len cur num2 (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len cur num2 (-1) ) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len cur num2 (-1) ) ”
.

Definition fruit_distribution_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (cur <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_11 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 cur (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 cur (-1) ) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ (num1 <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 cur (-1) ) ”
.

Definition fruit_distribution_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (cur <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_11_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_12 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur >= 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 num2 (-1) ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 num2 (-1) ) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (num1 <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 num2 (-1) ) ”
.

Definition fruit_distribution_entail_wit_12_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num2 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_12_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur >= 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_13 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num1 < 0)) (PreH2 : (cur < 0)) (PreH3 : (i >= len)) (PreH4 : (0 <= i)) (PreH5 : (i <= len)) (PreH6 : (len = (string_length (str_l)))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len 0 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur < 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len 0 num2 cur ) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num1 < 0)) (PreH3 : (cur < 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len 0 num2 cur ) ”
.

Definition fruit_distribution_entail_wit_14_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur < 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ” 
  &&  “ (num1 <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_14_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
.

Definition fruit_distribution_entail_wit_14_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_14_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num2 < 0)) (PreH2 : (num1 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 <= num1)) (PreH8 : (num1 <= INT_MAX)) (PreH9 : (cur = (-1))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_14_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
.

Definition fruit_distribution_entail_wit_14_3 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num2 < 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (num1 = 0)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_67_pre_z str_l n_pre )) (PreH10 : (fruit_safe_input_67 str_l n_pre )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (num1 = 0)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_14_3_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 < 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (num1 = 0)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 0 cur ) ”
.

Definition fruit_distribution_entail_wit_15_1 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (cur < 0)) (PreH4 : (i >= len)) (PreH5 : (0 <= i)) (PreH6 : (i <= len)) (PreH7 : (len = (string_length (str_l)))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (num1 <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_15_1_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ”
.

Definition fruit_distribution_entail_wit_15_1_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ”
.

Definition fruit_distribution_entail_wit_15_1_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= ((n_pre - num1 ) - num2 )) ”
.

Definition fruit_distribution_entail_wit_15_1_split_goal_4 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num2 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_15_1_split_goal_5 := 
forall (n_pre: Z) (str_l: (@list Z)) (num1: Z) (num2: Z) (cur: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (cur < 0)) (PreH5 : (i >= len)) (PreH6 : (0 <= i)) (PreH7 : (i <= len)) (PreH8 : (len = (string_length (str_l)))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre i num1 num2 cur )) ,
  TT && emp 
|--
  “ (num1 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_15_2 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 <= num1)) (PreH8 : (num1 <= INT_MAX)) (PreH9 : (0 <= num2)) (PreH10 : (num2 <= INT_MAX)) (PreH11 : (cur = (-1))) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= INT_MAX)) (PreH12 : (cur = (-1))) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_15_2_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= INT_MAX)) (PreH12 : (cur = (-1))) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ”
.

Definition fruit_distribution_entail_wit_15_2_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= INT_MAX)) (PreH12 : (cur = (-1))) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= ((n_pre - num1 ) - num2 )) ”
.

Definition fruit_distribution_entail_wit_15_3 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 <= num1)) (PreH8 : (num1 <= INT_MAX)) (PreH9 : (0 <= num2)) (PreH10 : (num2 <= INT_MAX)) (PreH11 : (cur = (-1))) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= INT_MAX)) (PreH12 : (cur = (-1))) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_15_3_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= INT_MAX)) (PreH12 : (cur = (-1))) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ”
.

Definition fruit_distribution_entail_wit_15_3_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (0 <= num2)) (PreH11 : (num2 <= INT_MAX)) (PreH12 : (cur = (-1))) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_67_pre_z str_l n_pre )) (PreH16 : (fruit_safe_input_67 str_l n_pre )) (PreH17 : ((string_length (str_l)) < INT_MAX)) (PreH18 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= ((n_pre - num1 ) - num2 )) ”
.

Definition fruit_distribution_entail_wit_15_4 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num2 >= 0)) (PreH2 : (num1 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 <= num1)) (PreH8 : (num1 <= INT_MAX)) (PreH9 : (cur = (-1))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_67_pre_z str_l n_pre )) (PreH13 : (fruit_safe_input_67 str_l n_pre )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (num2 <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_15_4_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ”
.

Definition fruit_distribution_entail_wit_15_4_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= ((n_pre - num1 ) - num2 )) ”
.

Definition fruit_distribution_entail_wit_15_4_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (num1 >= 0)) (PreH4 : (len = (string_length (str_l)))) (PreH5 : (i = len)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 <= num1)) (PreH9 : (num1 <= INT_MAX)) (PreH10 : (cur = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_67_pre_z str_l n_pre )) (PreH14 : (fruit_safe_input_67 str_l n_pre )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (num2 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_15_5 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (num2 >= 0)) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (num1 = 0)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_67_pre_z str_l n_pre )) (PreH10 : (fruit_safe_input_67 str_l n_pre )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (num1 = 0)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (num2 <= INT_MAX) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_15_5_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (num1 = 0)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ”
.

Definition fruit_distribution_entail_wit_15_5_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (num1 = 0)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= ((n_pre - num1 ) - num2 )) ”
.

Definition fruit_distribution_entail_wit_15_5_split_goal_3 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (cur: Z) (num2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (num2 >= 0)) (PreH3 : (len = (string_length (str_l)))) (PreH4 : (i = len)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (num1 = 0)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (num2 <= INT_MAX) ”
.

Definition fruit_distribution_entail_wit_15_6 := 
(
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= INT_MAX)) (PreH7 : (num2 = 0)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_67_pre_z str_l n_pre )) (PreH11 : (fruit_safe_input_67 str_l n_pre )) (PreH12 : ((string_length (str_l)) < INT_MAX)) (PreH13 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (len = (string_length (str_l))) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ (0 <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (fruit_scan_state_67 str_l n_pre len num1 num2 cur ) ”
  &&  (store_string s_pre str_l )
) \/
(
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (num2 = 0)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ” 
  &&  “ (0 <= ((n_pre - num1 ) - num2 )) ”
  &&  emp
).

Definition fruit_distribution_entail_wit_15_6_split_goal_1 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (num2 = 0)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ”
.

Definition fruit_distribution_entail_wit_15_6_split_goal_2 := 
forall (n_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (len = (string_length (str_l)))) (PreH3 : (i = len)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (0 <= num1)) (PreH7 : (num1 <= INT_MAX)) (PreH8 : (num2 = 0)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_67_pre_z str_l n_pre )) (PreH12 : (fruit_safe_input_67 str_l n_pre )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  TT && emp 
|--
  “ (0 <= ((n_pre - num1 ) - num2 )) ”
.

Definition fruit_distribution_return_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (len: Z) (i: Z) (num1: Z) (num2: Z) (cur: Z) (PreH1 : (len = (string_length (str_l)))) (PreH2 : (i = len)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= num1)) (PreH6 : (num1 <= INT_MAX)) (PreH7 : (0 <= num2)) (PreH8 : (num2 <= INT_MAX)) (PreH9 : (0 <= ((n_pre - num1 ) - num2 ))) (PreH10 : (((n_pre - num1 ) - num2 ) <= INT_MAX)) (PreH11 : (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) )) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_67_pre_z str_l n_pre )) (PreH15 : (fruit_safe_input_67 str_l n_pre )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (fruit_scan_state_67 str_l n_pre len num1 num2 cur )) ,
  (store_string s_pre str_l )
|--
  “ (0 <= ((n_pre - num1 ) - num2 )) ” 
  &&  “ (((n_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ (problem_67_spec_z str_l n_pre ((n_pre - num1 ) - num2 ) ) ”
  &&  (store_string s_pre str_l )
.

Definition fruit_distribution_partial_solve_wit_1_pure := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (problem_67_pre_z str_l n_pre )) (PreH6 : (fruit_safe_input_67 str_l n_pre )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition fruit_distribution_partial_solve_wit_1_aux := 
forall (n_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (problem_67_pre_z str_l n_pre )) (PreH6 : (fruit_safe_input_67 str_l n_pre )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (problem_67_pre_z str_l n_pre ) ” 
  &&  “ (fruit_safe_input_67 str_l n_pre ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  (store_string s_pre str_l )
.

Definition fruit_distribution_partial_solve_wit_1 := fruit_distribution_partial_solve_wit_1_pure -> fruit_distribution_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_fruit_distribution_safety_wit_1 : fruit_distribution_safety_wit_1.
Axiom proof_of_fruit_distribution_safety_wit_2 : fruit_distribution_safety_wit_2.
Axiom proof_of_fruit_distribution_safety_wit_3 : fruit_distribution_safety_wit_3.
Axiom proof_of_fruit_distribution_safety_wit_4 : fruit_distribution_safety_wit_4.
Axiom proof_of_fruit_distribution_safety_wit_5 : fruit_distribution_safety_wit_5.
Axiom proof_of_fruit_distribution_safety_wit_6 : fruit_distribution_safety_wit_6.
Axiom proof_of_fruit_distribution_safety_wit_7 : fruit_distribution_safety_wit_7.
Axiom proof_of_fruit_distribution_safety_wit_8 : fruit_distribution_safety_wit_8.
Axiom proof_of_fruit_distribution_safety_wit_9 : fruit_distribution_safety_wit_9.
Axiom proof_of_fruit_distribution_safety_wit_10 : fruit_distribution_safety_wit_10.
Axiom proof_of_fruit_distribution_safety_wit_11 : fruit_distribution_safety_wit_11.
Axiom proof_of_fruit_distribution_safety_wit_12 : fruit_distribution_safety_wit_12.
Axiom proof_of_fruit_distribution_safety_wit_13 : fruit_distribution_safety_wit_13.
Axiom proof_of_fruit_distribution_safety_wit_14 : fruit_distribution_safety_wit_14.
Axiom proof_of_fruit_distribution_safety_wit_15 : fruit_distribution_safety_wit_15.
Axiom proof_of_fruit_distribution_safety_wit_16 : fruit_distribution_safety_wit_16.
Axiom proof_of_fruit_distribution_safety_wit_17 : fruit_distribution_safety_wit_17.
Axiom proof_of_fruit_distribution_safety_wit_18 : fruit_distribution_safety_wit_18.
Axiom proof_of_fruit_distribution_safety_wit_19 : fruit_distribution_safety_wit_19.
Axiom proof_of_fruit_distribution_safety_wit_20 : fruit_distribution_safety_wit_20.
Axiom proof_of_fruit_distribution_safety_wit_21 : fruit_distribution_safety_wit_21.
Axiom proof_of_fruit_distribution_safety_wit_22 : fruit_distribution_safety_wit_22.
Axiom proof_of_fruit_distribution_safety_wit_23 : fruit_distribution_safety_wit_23.
Axiom proof_of_fruit_distribution_safety_wit_24 : fruit_distribution_safety_wit_24.
Axiom proof_of_fruit_distribution_safety_wit_25 : fruit_distribution_safety_wit_25.
Axiom proof_of_fruit_distribution_safety_wit_26 : fruit_distribution_safety_wit_26.
Axiom proof_of_fruit_distribution_safety_wit_27 : fruit_distribution_safety_wit_27.
Axiom proof_of_fruit_distribution_safety_wit_28 : fruit_distribution_safety_wit_28.
Axiom proof_of_fruit_distribution_safety_wit_29 : fruit_distribution_safety_wit_29.
Axiom proof_of_fruit_distribution_safety_wit_30 : fruit_distribution_safety_wit_30.
Axiom proof_of_fruit_distribution_safety_wit_31 : fruit_distribution_safety_wit_31.
Axiom proof_of_fruit_distribution_safety_wit_32 : fruit_distribution_safety_wit_32.
Axiom proof_of_fruit_distribution_safety_wit_33 : fruit_distribution_safety_wit_33.
Axiom proof_of_fruit_distribution_safety_wit_34 : fruit_distribution_safety_wit_34.
Axiom proof_of_fruit_distribution_safety_wit_35 : fruit_distribution_safety_wit_35.
Axiom proof_of_fruit_distribution_safety_wit_36 : fruit_distribution_safety_wit_36.
Axiom proof_of_fruit_distribution_safety_wit_37 : fruit_distribution_safety_wit_37.
Axiom proof_of_fruit_distribution_safety_wit_38 : fruit_distribution_safety_wit_38.
Axiom proof_of_fruit_distribution_safety_wit_39 : fruit_distribution_safety_wit_39.
Axiom proof_of_fruit_distribution_safety_wit_40 : fruit_distribution_safety_wit_40.
Axiom proof_of_fruit_distribution_safety_wit_41 : fruit_distribution_safety_wit_41.
Axiom proof_of_fruit_distribution_safety_wit_42 : fruit_distribution_safety_wit_42.
Axiom proof_of_fruit_distribution_safety_wit_43 : fruit_distribution_safety_wit_43.
Axiom proof_of_fruit_distribution_safety_wit_44 : fruit_distribution_safety_wit_44.
Axiom proof_of_fruit_distribution_safety_wit_45 : fruit_distribution_safety_wit_45.
Axiom proof_of_fruit_distribution_safety_wit_46 : fruit_distribution_safety_wit_46.
Axiom proof_of_fruit_distribution_safety_wit_47 : fruit_distribution_safety_wit_47.
Axiom proof_of_fruit_distribution_safety_wit_48 : fruit_distribution_safety_wit_48.
Axiom proof_of_fruit_distribution_safety_wit_49 : fruit_distribution_safety_wit_49.
Axiom proof_of_fruit_distribution_safety_wit_50 : fruit_distribution_safety_wit_50.
Axiom proof_of_fruit_distribution_safety_wit_51 : fruit_distribution_safety_wit_51.
Axiom proof_of_fruit_distribution_safety_wit_52 : fruit_distribution_safety_wit_52.
Axiom proof_of_fruit_distribution_safety_wit_53 : fruit_distribution_safety_wit_53.
Axiom proof_of_fruit_distribution_safety_wit_54 : fruit_distribution_safety_wit_54.
Axiom proof_of_fruit_distribution_safety_wit_55 : fruit_distribution_safety_wit_55.
Axiom proof_of_fruit_distribution_safety_wit_56 : fruit_distribution_safety_wit_56.
Axiom proof_of_fruit_distribution_safety_wit_57 : fruit_distribution_safety_wit_57.
Axiom proof_of_fruit_distribution_safety_wit_58 : fruit_distribution_safety_wit_58.
Axiom proof_of_fruit_distribution_safety_wit_59 : fruit_distribution_safety_wit_59.
Axiom proof_of_fruit_distribution_safety_wit_60 : fruit_distribution_safety_wit_60.
Axiom proof_of_fruit_distribution_safety_wit_61 : fruit_distribution_safety_wit_61.
Axiom proof_of_fruit_distribution_safety_wit_62 : fruit_distribution_safety_wit_62.
Axiom proof_of_fruit_distribution_safety_wit_63 : fruit_distribution_safety_wit_63.
Axiom proof_of_fruit_distribution_safety_wit_64 : fruit_distribution_safety_wit_64.
Axiom proof_of_fruit_distribution_safety_wit_65 : fruit_distribution_safety_wit_65.
Axiom proof_of_fruit_distribution_safety_wit_66 : fruit_distribution_safety_wit_66.
Axiom proof_of_fruit_distribution_safety_wit_67 : fruit_distribution_safety_wit_67.
Axiom proof_of_fruit_distribution_safety_wit_68 : fruit_distribution_safety_wit_68.
Axiom proof_of_fruit_distribution_entail_wit_1 : fruit_distribution_entail_wit_1.
Axiom proof_of_fruit_distribution_entail_wit_2 : fruit_distribution_entail_wit_2.
Axiom proof_of_fruit_distribution_entail_wit_3_1 : fruit_distribution_entail_wit_3_1.
Axiom proof_of_fruit_distribution_entail_wit_3_2 : fruit_distribution_entail_wit_3_2.
Axiom proof_of_fruit_distribution_entail_wit_4 : fruit_distribution_entail_wit_4.
Axiom proof_of_fruit_distribution_entail_wit_5_1 : fruit_distribution_entail_wit_5_1.
Axiom proof_of_fruit_distribution_entail_wit_5_2 : fruit_distribution_entail_wit_5_2.
Axiom proof_of_fruit_distribution_entail_wit_6_1 : fruit_distribution_entail_wit_6_1.
Axiom proof_of_fruit_distribution_entail_wit_6_2 : fruit_distribution_entail_wit_6_2.
Axiom proof_of_fruit_distribution_entail_wit_7_1 : fruit_distribution_entail_wit_7_1.
Axiom proof_of_fruit_distribution_entail_wit_7_2 : fruit_distribution_entail_wit_7_2.
Axiom proof_of_fruit_distribution_entail_wit_8_1 : fruit_distribution_entail_wit_8_1.
Axiom proof_of_fruit_distribution_entail_wit_8_2 : fruit_distribution_entail_wit_8_2.
Axiom proof_of_fruit_distribution_entail_wit_9_1 : fruit_distribution_entail_wit_9_1.
Axiom proof_of_fruit_distribution_entail_wit_9_2 : fruit_distribution_entail_wit_9_2.
Axiom proof_of_fruit_distribution_entail_wit_9_3 : fruit_distribution_entail_wit_9_3.
Axiom proof_of_fruit_distribution_entail_wit_9_4 : fruit_distribution_entail_wit_9_4.
Axiom proof_of_fruit_distribution_entail_wit_9_5 : fruit_distribution_entail_wit_9_5.
Axiom proof_of_fruit_distribution_entail_wit_10 : fruit_distribution_entail_wit_10.
Axiom proof_of_fruit_distribution_entail_wit_11 : fruit_distribution_entail_wit_11.
Axiom proof_of_fruit_distribution_entail_wit_12 : fruit_distribution_entail_wit_12.
Axiom proof_of_fruit_distribution_entail_wit_13 : fruit_distribution_entail_wit_13.
Axiom proof_of_fruit_distribution_entail_wit_14_1 : fruit_distribution_entail_wit_14_1.
Axiom proof_of_fruit_distribution_entail_wit_14_2 : fruit_distribution_entail_wit_14_2.
Axiom proof_of_fruit_distribution_entail_wit_14_3 : fruit_distribution_entail_wit_14_3.
Axiom proof_of_fruit_distribution_entail_wit_15_1 : fruit_distribution_entail_wit_15_1.
Axiom proof_of_fruit_distribution_entail_wit_15_2 : fruit_distribution_entail_wit_15_2.
Axiom proof_of_fruit_distribution_entail_wit_15_3 : fruit_distribution_entail_wit_15_3.
Axiom proof_of_fruit_distribution_entail_wit_15_4 : fruit_distribution_entail_wit_15_4.
Axiom proof_of_fruit_distribution_entail_wit_15_5 : fruit_distribution_entail_wit_15_5.
Axiom proof_of_fruit_distribution_entail_wit_15_6 : fruit_distribution_entail_wit_15_6.
Axiom proof_of_fruit_distribution_return_wit_1 : fruit_distribution_return_wit_1.
Axiom proof_of_fruit_distribution_partial_solve_wit_1_pure : fruit_distribution_partial_solve_wit_1_pure.
Axiom proof_of_fruit_distribution_partial_solve_wit_1 : fruit_distribution_partial_solve_wit_1.

End VC_Correct.
