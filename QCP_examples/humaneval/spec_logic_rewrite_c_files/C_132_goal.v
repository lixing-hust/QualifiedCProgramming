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
Require Import coins_132.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function is_nested -----*)

Definition is_nested_safety_wit_1 := 
forall (str_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "count" ) )) # Int  |->_)
  **  (store_string str_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_2 := 
forall (str_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "maxcount" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (store_string str_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_3 := 
forall (str_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "maxcount" ) )) # Int  |-> 0)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (store_string str_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_4 := 
forall (str_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "maxcount" ) )) # Int  |-> 0)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (store_string str_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_5 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (91 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 91) ”
.

Definition is_nested_safety_wit_6 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 91)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string input )) (PreH12 : (problem_132_pre_z input )) (PreH13 : (bracket_codes_z_132 input )) (PreH14 : ((string_length (input)) < INT_MAX)) (PreH15 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition is_nested_safety_wit_7 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 91)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string input )) (PreH12 : (problem_132_pre_z input )) (PreH13 : (bracket_codes_z_132 input )) (PreH14 : ((string_length (input)) < INT_MAX)) (PreH15 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_nested_safety_wit_8 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 91)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string input )) (PreH12 : (problem_132_pre_z input )) (PreH13 : (bracket_codes_z_132 input )) (PreH14 : ((string_length (input)) < INT_MAX)) (PreH15 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (93 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 93) ”
.

Definition is_nested_safety_wit_9 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 91)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string input )) (PreH12 : (problem_132_pre_z input )) (PreH13 : (bracket_codes_z_132 input )) (PreH14 : ((string_length (input)) < INT_MAX)) (PreH15 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (93 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 93) ”
.

Definition is_nested_safety_wit_10 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 93)) (PreH2 : ((Znth i (c_string (input)) 0) = 91)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= maxcount)) (PreH9 : (maxcount <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string input )) (PreH13 : (problem_132_pre_z input )) (PreH14 : (bracket_codes_z_132 input )) (PreH15 : ((string_length (input)) < INT_MAX)) (PreH16 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ False ”
.

Definition is_nested_safety_wit_11 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 93)) (PreH2 : ((Znth i (c_string (input)) 0) <> 91)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= maxcount)) (PreH9 : (maxcount <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string input )) (PreH13 : (problem_132_pre_z input )) (PreH14 : (bracket_codes_z_132 input )) (PreH15 : ((string_length (input)) < INT_MAX)) (PreH16 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition is_nested_safety_wit_12 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 93)) (PreH2 : ((Znth i (c_string (input)) 0) <> 91)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= maxcount)) (PreH9 : (maxcount <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string input )) (PreH13 : (problem_132_pre_z input )) (PreH14 : (bracket_codes_z_132 input )) (PreH15 : ((string_length (input)) < INT_MAX)) (PreH16 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_nested_safety_wit_13 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 93)) (PreH2 : ((Znth i (c_string (input)) 0) <> 91)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= maxcount)) (PreH9 : (maxcount <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string input )) (PreH13 : (problem_132_pre_z input )) (PreH14 : (bracket_codes_z_132 input )) (PreH15 : ((string_length (input)) < INT_MAX)) (PreH16 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_14 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 93)) (PreH2 : ((Znth i (c_string (input)) 0) = 91)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= maxcount)) (PreH9 : (maxcount <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string input )) (PreH13 : (problem_132_pre_z input )) (PreH14 : (bracket_codes_z_132 input )) (PreH15 : ((string_length (input)) < INT_MAX)) (PreH16 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_15 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 93)) (PreH2 : ((Znth i (c_string (input)) 0) <> 91)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= count)) (PreH8 : (count <= maxcount)) (PreH9 : (maxcount <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string input )) (PreH13 : (problem_132_pre_z input )) (PreH14 : (bracket_codes_z_132 input )) (PreH15 : ((string_length (input)) < INT_MAX)) (PreH16 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_16 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 93)) (PreH3 : ((Znth i (c_string (input)) 0) = 91)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= count)) (PreH9 : (count <= maxcount)) (PreH10 : (maxcount <= i)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string input )) (PreH14 : (problem_132_pre_z input )) (PreH15 : (bracket_codes_z_132 input )) (PreH16 : ((string_length (input)) < INT_MAX)) (PreH17 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ False ”
.

Definition is_nested_safety_wit_17 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (count < 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 93)) (PreH3 : ((Znth i (c_string (input)) 0) <> 91)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= count)) (PreH9 : (count <= maxcount)) (PreH10 : (maxcount <= i)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string input )) (PreH14 : (problem_132_pre_z input )) (PreH15 : (bracket_codes_z_132 input )) (PreH16 : ((string_length (input)) < INT_MAX)) (PreH17 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ False ”
.

Definition is_nested_safety_wit_18 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 93)) (PreH3 : ((Znth i (c_string (input)) 0) <> 91)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= count)) (PreH9 : (count <= maxcount)) (PreH10 : (maxcount <= i)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string input )) (PreH14 : (problem_132_pre_z input )) (PreH15 : (bracket_codes_z_132 input )) (PreH16 : ((string_length (input)) < INT_MAX)) (PreH17 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_safety_wit_19 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (0 > maxcount)) (PreH2 : ((count - 1 ) < 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 93)) (PreH4 : ((Znth i (c_string (input)) 0) <> 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ False ”
.

Definition is_nested_safety_wit_20 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((count - 1 ) > maxcount)) (PreH2 : ((count - 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 93)) (PreH4 : ((Znth i (c_string (input)) 0) <> 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ False ”
.

Definition is_nested_safety_wit_21 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (count > maxcount)) (PreH2 : (count >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 93)) (PreH4 : ((Znth i (c_string (input)) 0) <> 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  (store_string str_pre input )
|--
  “ False ”
.

Definition is_nested_safety_wit_22 := 
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= count)) (PreH5 : (count <= maxcount)) (PreH6 : (maxcount <= (i + 1 ))) (PreH7 : (ch = 91)) (PreH8 : (valid_string input )) (PreH9 : (problem_132_pre_z input )) (PreH10 : (bracket_codes_z_132 input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string str_pre input )
|--
  “ ((maxcount - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maxcount - 2 )) ”
.

Definition is_nested_safety_wit_23 := 
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= count)) (PreH5 : (count <= maxcount)) (PreH6 : (maxcount <= (i + 1 ))) (PreH7 : (ch = 93)) (PreH8 : (valid_string input )) (PreH9 : (problem_132_pre_z input )) (PreH10 : (bracket_codes_z_132 input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string str_pre input )
|--
  “ ((maxcount - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maxcount - 2 )) ”
.

Definition is_nested_safety_wit_24 := 
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= count)) (PreH5 : (count <= maxcount)) (PreH6 : (maxcount <= (i + 1 ))) (PreH7 : (ch = 93)) (PreH8 : (valid_string input )) (PreH9 : (problem_132_pre_z input )) (PreH10 : (bracket_codes_z_132 input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string str_pre input )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition is_nested_safety_wit_25 := 
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (n = (string_length (input)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= count)) (PreH5 : (count <= maxcount)) (PreH6 : (maxcount <= (i + 1 ))) (PreH7 : (ch = 91)) (PreH8 : (valid_string input )) (PreH9 : (problem_132_pre_z input )) (PreH10 : (bracket_codes_z_132 input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string str_pre input )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition is_nested_safety_wit_26 := 
forall (str_pre: Z) (input: (@list Z)) (n_addr_v: Z) (count_addr_v: Z) (maxcount_addr_v: Z) (i_addr_v: Z) (ch_addr_v: Z) (PreH1 : (problem_132_result_z input 1 )) ,
  (store_string str_pre input )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n_addr_v)
  **  ((( &( "count" ) )) # Int  |-> count_addr_v)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_nested_safety_wit_27 := 
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (count > (maxcount - 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= (i + 1 ))) (PreH8 : (ch = 93)) (PreH9 : (valid_string input )) (PreH10 : (problem_132_pre_z input )) (PreH11 : (bracket_codes_z_132 input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string str_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_nested_safety_wit_28 := 
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (count > (maxcount - 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= (i + 1 ))) (PreH8 : (ch = 91)) (PreH9 : (valid_string input )) (PreH10 : (problem_132_pre_z input )) (PreH11 : (bracket_codes_z_132 input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string str_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_nested_safety_wit_29 := 
forall (str_pre: Z) (input: (@list Z)) (n_addr_v: Z) (count_addr_v: Z) (maxcount_addr_v: Z) (i_addr_v: Z) (ch_addr_v: Z) (PreH1 : (problem_132_result_z input 0 )) ,
  (store_string str_pre input )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> n_addr_v)
  **  ((( &( "count" ) )) # Int  |-> count_addr_v)
  **  ((( &( "maxcount" ) )) # Int  |-> maxcount_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_nested_entail_wit_1 := 
(
forall (str_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  (store_string str_pre input )
|--
  “ (retval = (string_length (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_state_132 input 0 0 0 ) ”
  &&  (store_string str_pre input )
) \/
(
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (nested_scan_state_132 input 0 0 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition is_nested_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (nested_scan_state_132 input 0 0 0 ) ”
.

Definition is_nested_entail_wit_1_split_goal_2 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_132_pre_z input )) (PreH5 : (bracket_codes_z_132 input )) (PreH6 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition is_nested_entail_wit_2_1 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (count <= maxcount)) (PreH2 : (count >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 93)) (PreH4 : ((Znth i (c_string (input)) 0) <> 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  (store_string str_pre input )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 93) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) count maxcount ) ”
  &&  (store_string str_pre input ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 91) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) count maxcount ) ”
  &&  (store_string str_pre input ))
.

Definition is_nested_entail_wit_2_2 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((count + 1 ) <= maxcount)) (PreH2 : ((count + 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 93)) (PreH4 : ((Znth i (c_string (input)) 0) = 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  (store_string str_pre input )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 93) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) (count + 1 ) maxcount ) ”
  &&  (store_string str_pre input ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 91) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) (count + 1 ) maxcount ) ”
  &&  (store_string str_pre input ))
.

Definition is_nested_entail_wit_2_3 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((count - 1 ) <= maxcount)) (PreH2 : ((count - 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 93)) (PreH4 : ((Znth i (c_string (input)) 0) <> 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  (store_string str_pre input )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 93) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) (count - 1 ) maxcount ) ”
  &&  (store_string str_pre input ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 91) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) (count - 1 ) maxcount ) ”
  &&  (store_string str_pre input ))
.

Definition is_nested_entail_wit_2_4 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (0 <= maxcount)) (PreH2 : ((count - 1 ) < 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 93)) (PreH4 : ((Znth i (c_string (input)) 0) <> 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  (store_string str_pre input )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 93) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) 0 maxcount ) ”
  &&  (store_string str_pre input ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 91) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) 0 maxcount ) ”
  &&  (store_string str_pre input ))
.

Definition is_nested_entail_wit_2_5 := 
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : ((count + 1 ) > maxcount)) (PreH2 : ((count + 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 93)) (PreH4 : ((Znth i (c_string (input)) 0) = 91)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= count)) (PreH10 : (count <= maxcount)) (PreH11 : (maxcount <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string input )) (PreH15 : (problem_132_pre_z input )) (PreH16 : (bracket_codes_z_132 input )) (PreH17 : ((string_length (input)) < INT_MAX)) (PreH18 : (nested_scan_state_132 input i count maxcount )) ,
  (store_string str_pre input )
|--
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 93) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) (count + 1 ) (count + 1 ) ) ”
  &&  (store_string str_pre input ))
  ||
  (“ (n = (string_length (input))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 91) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_after_132 input (i + 1 ) (count + 1 ) (count + 1 ) ) ”
  &&  (store_string str_pre input ))
.

Definition is_nested_entail_wit_3_1 := 
(
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (count <= (maxcount - 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= (i + 1 ))) (PreH8 : (ch = 91)) (PreH9 : (valid_string input )) (PreH10 : (problem_132_pre_z input )) (PreH11 : (bracket_codes_z_132 input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  (store_string str_pre input )
|--
  “ (problem_132_result_z input 1 ) ”
  &&  (store_string str_pre input )
) \/
(
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count <= (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 91)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (problem_132_result_z input 1 ) ”
  &&  emp
).

Definition is_nested_entail_wit_3_1_split_goal_1 := 
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count <= (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 91)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (problem_132_result_z input 1 ) ”
.

Definition is_nested_entail_wit_3_2 := 
(
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (count <= (maxcount - 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= (i + 1 ))) (PreH8 : (ch = 93)) (PreH9 : (valid_string input )) (PreH10 : (problem_132_pre_z input )) (PreH11 : (bracket_codes_z_132 input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  (store_string str_pre input )
|--
  “ (problem_132_result_z input 1 ) ”
  &&  (store_string str_pre input )
) \/
(
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count <= (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 93)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (problem_132_result_z input 1 ) ”
  &&  emp
).

Definition is_nested_entail_wit_3_2_split_goal_1 := 
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count <= (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 93)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (problem_132_result_z input 1 ) ”
.

Definition is_nested_entail_wit_4_1 := 
(
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (count > (maxcount - 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= (i + 1 ))) (PreH8 : (ch = 93)) (PreH9 : (valid_string input )) (PreH10 : (problem_132_pre_z input )) (PreH11 : (bracket_codes_z_132 input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  (store_string str_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_state_132 input (i + 1 ) count maxcount ) ”
  &&  (store_string str_pre input )
) \/
(
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count > (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 93)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (nested_scan_state_132 input (i + 1 ) count maxcount ) ”
  &&  emp
).

Definition is_nested_entail_wit_4_1_split_goal_1 := 
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count > (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 93)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (nested_scan_state_132 input (i + 1 ) count maxcount ) ”
.

Definition is_nested_entail_wit_4_2 := 
(
forall (str_pre: Z) (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (count > (maxcount - 2 ))) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= (i + 1 ))) (PreH8 : (ch = 91)) (PreH9 : (valid_string input )) (PreH10 : (problem_132_pre_z input )) (PreH11 : (bracket_codes_z_132 input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  (store_string str_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= maxcount) ” 
  &&  “ (maxcount <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (nested_scan_state_132 input (i + 1 ) count maxcount ) ”
  &&  (store_string str_pre input )
) \/
(
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count > (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 91)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (nested_scan_state_132 input (i + 1 ) count maxcount ) ”
  &&  emp
).

Definition is_nested_entail_wit_4_2_split_goal_1 := 
forall (input: (@list Z)) (n: Z) (i: Z) (count: Z) (maxcount: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (count > (maxcount - 2 ))) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= (i + 1 ))) (PreH9 : (ch = 91)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_after_132 input (i + 1 ) count maxcount )) ,
  TT && emp 
|--
  “ (nested_scan_state_132 input (i + 1 ) count maxcount ) ”
.

Definition is_nested_entail_wit_5 := 
(
forall (str_pre: Z) (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= count)) (PreH6 : (count <= maxcount)) (PreH7 : (maxcount <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string input )) (PreH11 : (problem_132_pre_z input )) (PreH12 : (bracket_codes_z_132 input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (nested_scan_state_132 input i count maxcount )) ,
  (store_string str_pre input )
|--
  “ (problem_132_result_z input 0 ) ”
  &&  (store_string str_pre input )
) \/
(
forall (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string input )) (PreH12 : (problem_132_pre_z input )) (PreH13 : (bracket_codes_z_132 input )) (PreH14 : ((string_length (input)) < INT_MAX)) (PreH15 : (nested_scan_state_132 input i count maxcount )) ,
  TT && emp 
|--
  “ (problem_132_result_z input 0 ) ”
  &&  emp
).

Definition is_nested_entail_wit_5_split_goal_1 := 
forall (input: (@list Z)) (ch: Z) (maxcount: Z) (count: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= count)) (PreH7 : (count <= maxcount)) (PreH8 : (maxcount <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string input )) (PreH12 : (problem_132_pre_z input )) (PreH13 : (bracket_codes_z_132 input )) (PreH14 : ((string_length (input)) < INT_MAX)) (PreH15 : (nested_scan_state_132 input i count maxcount )) ,
  TT && emp 
|--
  “ (problem_132_result_z input 0 ) ”
.

Definition is_nested_return_wit_1 := 
forall (str_pre: Z) (input: (@list Z)) (PreH1 : (problem_132_result_z input 0 )) ,
  (store_string str_pre input )
|--
  “ (problem_132_result_z input 0 ) ”
  &&  (store_string str_pre input )
.

Definition is_nested_return_wit_2 := 
forall (str_pre: Z) (input: (@list Z)) (PreH1 : (problem_132_result_z input 1 )) ,
  (store_string str_pre input )
|--
  “ (problem_132_result_z input 1 ) ”
  &&  (store_string str_pre input )
.

Definition is_nested_partial_solve_wit_1_pure := 
forall (str_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_132_pre_z input )) (PreH3 : (bracket_codes_z_132 input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (store_string str_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition is_nested_partial_solve_wit_1_aux := 
forall (str_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_132_pre_z input )) (PreH3 : (bracket_codes_z_132 input )) (PreH4 : ((string_length (input)) < INT_MAX)) ,
  (store_string str_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_132_pre_z input ) ” 
  &&  “ (bracket_codes_z_132 input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string str_pre input )
.

Definition is_nested_partial_solve_wit_1 := is_nested_partial_solve_wit_1_pure -> is_nested_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_is_nested_safety_wit_1 : is_nested_safety_wit_1.
Axiom proof_of_is_nested_safety_wit_2 : is_nested_safety_wit_2.
Axiom proof_of_is_nested_safety_wit_3 : is_nested_safety_wit_3.
Axiom proof_of_is_nested_safety_wit_4 : is_nested_safety_wit_4.
Axiom proof_of_is_nested_safety_wit_5 : is_nested_safety_wit_5.
Axiom proof_of_is_nested_safety_wit_6 : is_nested_safety_wit_6.
Axiom proof_of_is_nested_safety_wit_7 : is_nested_safety_wit_7.
Axiom proof_of_is_nested_safety_wit_8 : is_nested_safety_wit_8.
Axiom proof_of_is_nested_safety_wit_9 : is_nested_safety_wit_9.
Axiom proof_of_is_nested_safety_wit_10 : is_nested_safety_wit_10.
Axiom proof_of_is_nested_safety_wit_11 : is_nested_safety_wit_11.
Axiom proof_of_is_nested_safety_wit_12 : is_nested_safety_wit_12.
Axiom proof_of_is_nested_safety_wit_13 : is_nested_safety_wit_13.
Axiom proof_of_is_nested_safety_wit_14 : is_nested_safety_wit_14.
Axiom proof_of_is_nested_safety_wit_15 : is_nested_safety_wit_15.
Axiom proof_of_is_nested_safety_wit_16 : is_nested_safety_wit_16.
Axiom proof_of_is_nested_safety_wit_17 : is_nested_safety_wit_17.
Axiom proof_of_is_nested_safety_wit_18 : is_nested_safety_wit_18.
Axiom proof_of_is_nested_safety_wit_19 : is_nested_safety_wit_19.
Axiom proof_of_is_nested_safety_wit_20 : is_nested_safety_wit_20.
Axiom proof_of_is_nested_safety_wit_21 : is_nested_safety_wit_21.
Axiom proof_of_is_nested_safety_wit_22 : is_nested_safety_wit_22.
Axiom proof_of_is_nested_safety_wit_23 : is_nested_safety_wit_23.
Axiom proof_of_is_nested_safety_wit_24 : is_nested_safety_wit_24.
Axiom proof_of_is_nested_safety_wit_25 : is_nested_safety_wit_25.
Axiom proof_of_is_nested_safety_wit_26 : is_nested_safety_wit_26.
Axiom proof_of_is_nested_safety_wit_27 : is_nested_safety_wit_27.
Axiom proof_of_is_nested_safety_wit_28 : is_nested_safety_wit_28.
Axiom proof_of_is_nested_safety_wit_29 : is_nested_safety_wit_29.
Axiom proof_of_is_nested_entail_wit_1 : is_nested_entail_wit_1.
Axiom proof_of_is_nested_entail_wit_2_1 : is_nested_entail_wit_2_1.
Axiom proof_of_is_nested_entail_wit_2_2 : is_nested_entail_wit_2_2.
Axiom proof_of_is_nested_entail_wit_2_3 : is_nested_entail_wit_2_3.
Axiom proof_of_is_nested_entail_wit_2_4 : is_nested_entail_wit_2_4.
Axiom proof_of_is_nested_entail_wit_2_5 : is_nested_entail_wit_2_5.
Axiom proof_of_is_nested_entail_wit_3_1 : is_nested_entail_wit_3_1.
Axiom proof_of_is_nested_entail_wit_3_2 : is_nested_entail_wit_3_2.
Axiom proof_of_is_nested_entail_wit_4_1 : is_nested_entail_wit_4_1.
Axiom proof_of_is_nested_entail_wit_4_2 : is_nested_entail_wit_4_2.
Axiom proof_of_is_nested_entail_wit_5 : is_nested_entail_wit_5.
Axiom proof_of_is_nested_return_wit_1 : is_nested_return_wit_1.
Axiom proof_of_is_nested_return_wit_2 : is_nested_return_wit_2.
Axiom proof_of_is_nested_partial_solve_wit_1_pure : is_nested_partial_solve_wit_1_pure.
Axiom proof_of_is_nested_partial_solve_wit_1 : is_nested_partial_solve_wit_1.

End VC_Correct.
