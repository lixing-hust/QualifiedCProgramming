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
Require Import coins_61.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function correct_bracketing -----*)

Definition correct_bracketing_safety_wit_1 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "level" ) )) # Int  |->_)
  **  (store_string brackets_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_2 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  (store_string brackets_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_3 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  (store_string brackets_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_4 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (0 <= level)) (PreH6 : (level <= i)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_61_pre_z str_l )) (PreH12 : (bracket_safe_input_61 str_l )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (bracket_state_61 str_l i level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string brackets_pre str_l )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition correct_bracketing_safety_wit_5 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string brackets_pre str_l )
|--
  “ ((level + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level + 1 )) ”
.

Definition correct_bracketing_safety_wit_6 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string brackets_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition correct_bracketing_safety_wit_7 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string brackets_pre str_l )
|--
  “ ((level - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level - 1 )) ”
.

Definition correct_bracketing_safety_wit_8 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string brackets_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition correct_bracketing_safety_wit_9 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string brackets_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_10 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (i: Z) (n: Z) (level: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (level = (-1))) (PreH5 : (ch = 41)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (problem_61_pre_z str_l )) (PreH9 : (bracket_safe_input_61 str_l )) (PreH10 : ((string_length (str_l)) < INT_MAX)) (PreH11 : (problem_61_spec_z str_l false )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string brackets_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_11 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (i: Z) (n: Z) (level: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (1 <= level)) (PreH5 : (level <= (i + 1 ))) (PreH6 : (ch = 40)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_61_pre_z str_l )) (PreH10 : (bracket_safe_input_61 str_l )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (bracket_state_61 str_l (i + 1 ) level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string brackets_pre str_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition correct_bracketing_safety_wit_12 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (i: Z) (n: Z) (level: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (0 <= level)) (PreH5 : (level <= i)) (PreH6 : (ch = 41)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_61_pre_z str_l )) (PreH10 : (bracket_safe_input_61 str_l )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (bracket_state_61 str_l (i + 1 ) level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string brackets_pre str_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition correct_bracketing_safety_wit_13 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (0 <= level)) (PreH6 : (level <= i)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_61_pre_z str_l )) (PreH12 : (bracket_safe_input_61 str_l )) (PreH13 : ((string_length (str_l)) < INT_MAX)) (PreH14 : (bracket_state_61 str_l i level )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string brackets_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_14 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (n: Z) (level: Z) (ch: Z) (i_addr_v: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (level <> 0)) (PreH3 : (0 < level)) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_61_pre_z str_l )) (PreH7 : (bracket_safe_input_61 str_l )) (PreH8 : ((string_length (str_l)) < INT_MAX)) (PreH9 : (bracket_state_61 str_l n level )) (PreH10 : (problem_61_spec_z str_l false )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string brackets_pre str_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_15 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (n: Z) (level: Z) (ch: Z) (i_addr_v: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (level = 0)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) (PreH8 : (bracket_state_61 str_l n 0 )) (PreH9 : (problem_61_spec_z str_l true )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string brackets_pre str_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition correct_bracketing_entail_wit_1 := 
(
forall (brackets_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string brackets_pre str_l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (bracket_state_61 str_l 0 0 ) ”
  &&  (store_string brackets_pre str_l )
) \/
(
forall (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l 0 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_1_split_goal_1 := 
forall (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l 0 0 ) ”
.

Definition correct_bracketing_entail_wit_1_split_goal_2 := 
forall (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition correct_bracketing_entail_wit_2 := 
(
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  (store_string brackets_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (1 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 40) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (bracket_state_61 str_l (i + 1 ) (level + 1 ) ) ”
  &&  (store_string brackets_pre str_l )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l (i + 1 ) (level + 1 ) ) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_2_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l (i + 1 ) (level + 1 ) ) ”
.

Definition correct_bracketing_entail_wit_3 := 
(
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  (store_string brackets_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ ((level - 1 ) = (-1)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (problem_61_spec_z str_l false ) ”
  &&  (store_string brackets_pre str_l )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_61_pre_z str_l )) (PreH15 : (bracket_safe_input_61 str_l )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (problem_61_spec_z str_l false ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_3_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_61_pre_z str_l )) (PreH15 : (bracket_safe_input_61 str_l )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (problem_61_spec_z str_l false ) ”
.

Definition correct_bracketing_entail_wit_3_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_61_pre_z str_l )) (PreH15 : (bracket_safe_input_61 str_l )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) = 41) ”
.

Definition correct_bracketing_entail_wit_4 := 
(
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  (store_string brackets_pre str_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= (level - 1 )) ” 
  &&  “ ((level - 1 ) <= i) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (bracket_state_61 str_l (i + 1 ) (level - 1 ) ) ”
  &&  (store_string brackets_pre str_l )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_61_pre_z str_l )) (PreH15 : (bracket_safe_input_61 str_l )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l (i + 1 ) (level - 1 ) ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_4_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_61_pre_z str_l )) (PreH15 : (bracket_safe_input_61 str_l )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l (i + 1 ) (level - 1 ) ) ”
.

Definition correct_bracketing_entail_wit_4_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (problem_61_pre_z str_l )) (PreH15 : (bracket_safe_input_61 str_l )) (PreH16 : ((string_length (str_l)) < INT_MAX)) (PreH17 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) = 41) ”
.

Definition correct_bracketing_entail_wit_5_1 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (i: Z) (n: Z) (level: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (1 <= level)) (PreH5 : (level <= (i + 1 ))) (PreH6 : (ch = 40)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_61_pre_z str_l )) (PreH10 : (bracket_safe_input_61 str_l )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (bracket_state_61 str_l (i + 1 ) level )) ,
  (store_string brackets_pre str_l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (bracket_state_61 str_l (i + 1 ) level ) ”
  &&  (store_string brackets_pre str_l )
.

Definition correct_bracketing_entail_wit_5_2 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (i: Z) (n: Z) (level: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (0 <= level)) (PreH5 : (level <= i)) (PreH6 : (ch = 41)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_61_pre_z str_l )) (PreH10 : (bracket_safe_input_61 str_l )) (PreH11 : ((string_length (str_l)) < INT_MAX)) (PreH12 : (bracket_state_61 str_l (i + 1 ) level )) ,
  (store_string brackets_pre str_l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (bracket_state_61 str_l (i + 1 ) level ) ”
  &&  (store_string brackets_pre str_l )
.

Definition correct_bracketing_entail_wit_6 := 
(
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (level <> 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  (store_string brackets_pre str_l )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (level <> 0) ” 
  &&  “ (0 < level) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (bracket_state_61 str_l n level ) ” 
  &&  “ (problem_61_spec_z str_l false ) ”
  &&  (store_string brackets_pre str_l )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level <> 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (problem_61_spec_z str_l false ) ” 
  &&  “ (bracket_state_61 str_l n level ) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_6_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level <> 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (problem_61_spec_z str_l false ) ”
.

Definition correct_bracketing_entail_wit_6_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level <> 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l n level ) ”
.

Definition correct_bracketing_entail_wit_7 := 
(
forall (brackets_pre: Z) (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (level = 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_61_pre_z str_l )) (PreH13 : (bracket_safe_input_61 str_l )) (PreH14 : ((string_length (str_l)) < INT_MAX)) (PreH15 : (bracket_state_61 str_l i level )) ,
  (store_string brackets_pre str_l )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (level = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (bracket_state_61 str_l n 0 ) ” 
  &&  “ (problem_61_spec_z str_l true ) ”
  &&  (store_string brackets_pre str_l )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level = 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (problem_61_spec_z str_l true ) ” 
  &&  “ (bracket_state_61 str_l n 0 ) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_7_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level = 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (problem_61_spec_z str_l true ) ”
.

Definition correct_bracketing_entail_wit_7_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (level: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level = 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (problem_61_pre_z str_l )) (PreH14 : (bracket_safe_input_61 str_l )) (PreH15 : ((string_length (str_l)) < INT_MAX)) (PreH16 : (bracket_state_61 str_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_61 str_l n 0 ) ”
.

Definition correct_bracketing_return_wit_1 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (n: Z) (level: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (level = 0)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_61_pre_z str_l )) (PreH6 : (bracket_safe_input_61 str_l )) (PreH7 : ((string_length (str_l)) < INT_MAX)) (PreH8 : (bracket_state_61 str_l n 0 )) (PreH9 : (problem_61_spec_z str_l true )) ,
  (store_string brackets_pre str_l )
|--
  (“ (1 = 0) ” 
  &&  “ (problem_61_spec_z str_l false ) ”
  &&  (store_string brackets_pre str_l ))
  ||
  (“ (1 <> 0) ” 
  &&  “ (problem_61_spec_z str_l true ) ”
  &&  (store_string brackets_pre str_l ))
.

Definition correct_bracketing_return_wit_2 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (n: Z) (level: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (level <> 0)) (PreH3 : (0 < level)) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_61_pre_z str_l )) (PreH7 : (bracket_safe_input_61 str_l )) (PreH8 : ((string_length (str_l)) < INT_MAX)) (PreH9 : (bracket_state_61 str_l n level )) (PreH10 : (problem_61_spec_z str_l false )) ,
  (store_string brackets_pre str_l )
|--
  (“ (0 = 0) ” 
  &&  “ (problem_61_spec_z str_l false ) ”
  &&  (store_string brackets_pre str_l ))
  ||
  (“ (0 <> 0) ” 
  &&  “ (problem_61_spec_z str_l true ) ”
  &&  (store_string brackets_pre str_l ))
.

Definition correct_bracketing_return_wit_3 := 
forall (brackets_pre: Z) (str_l: (@list Z)) (i: Z) (n: Z) (level: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (level = (-1))) (PreH5 : (ch = 41)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (problem_61_pre_z str_l )) (PreH9 : (bracket_safe_input_61 str_l )) (PreH10 : ((string_length (str_l)) < INT_MAX)) (PreH11 : (problem_61_spec_z str_l false )) ,
  (store_string brackets_pre str_l )
|--
  (“ (0 = 0) ” 
  &&  “ (problem_61_spec_z str_l false ) ”
  &&  (store_string brackets_pre str_l ))
  ||
  (“ (0 <> 0) ” 
  &&  “ (problem_61_spec_z str_l true ) ”
  &&  (store_string brackets_pre str_l ))
.

Definition correct_bracketing_partial_solve_wit_1_pure := 
forall (brackets_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_61_pre_z str_l )) (PreH4 : (bracket_safe_input_61 str_l )) (PreH5 : ((string_length (str_l)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  (store_string brackets_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition correct_bracketing_partial_solve_wit_1_aux := 
forall (brackets_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_61_pre_z str_l )) (PreH4 : (bracket_safe_input_61 str_l )) (PreH5 : ((string_length (str_l)) < INT_MAX)) ,
  (store_string brackets_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_61_pre_z str_l ) ” 
  &&  “ (bracket_safe_input_61 str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  (store_string brackets_pre str_l )
.

Definition correct_bracketing_partial_solve_wit_1 := correct_bracketing_partial_solve_wit_1_pure -> correct_bracketing_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_correct_bracketing_safety_wit_1 : correct_bracketing_safety_wit_1.
Axiom proof_of_correct_bracketing_safety_wit_2 : correct_bracketing_safety_wit_2.
Axiom proof_of_correct_bracketing_safety_wit_3 : correct_bracketing_safety_wit_3.
Axiom proof_of_correct_bracketing_safety_wit_4 : correct_bracketing_safety_wit_4.
Axiom proof_of_correct_bracketing_safety_wit_5 : correct_bracketing_safety_wit_5.
Axiom proof_of_correct_bracketing_safety_wit_6 : correct_bracketing_safety_wit_6.
Axiom proof_of_correct_bracketing_safety_wit_7 : correct_bracketing_safety_wit_7.
Axiom proof_of_correct_bracketing_safety_wit_8 : correct_bracketing_safety_wit_8.
Axiom proof_of_correct_bracketing_safety_wit_9 : correct_bracketing_safety_wit_9.
Axiom proof_of_correct_bracketing_safety_wit_10 : correct_bracketing_safety_wit_10.
Axiom proof_of_correct_bracketing_safety_wit_11 : correct_bracketing_safety_wit_11.
Axiom proof_of_correct_bracketing_safety_wit_12 : correct_bracketing_safety_wit_12.
Axiom proof_of_correct_bracketing_safety_wit_13 : correct_bracketing_safety_wit_13.
Axiom proof_of_correct_bracketing_safety_wit_14 : correct_bracketing_safety_wit_14.
Axiom proof_of_correct_bracketing_safety_wit_15 : correct_bracketing_safety_wit_15.
Axiom proof_of_correct_bracketing_entail_wit_1 : correct_bracketing_entail_wit_1.
Axiom proof_of_correct_bracketing_entail_wit_2 : correct_bracketing_entail_wit_2.
Axiom proof_of_correct_bracketing_entail_wit_3 : correct_bracketing_entail_wit_3.
Axiom proof_of_correct_bracketing_entail_wit_4 : correct_bracketing_entail_wit_4.
Axiom proof_of_correct_bracketing_entail_wit_5_1 : correct_bracketing_entail_wit_5_1.
Axiom proof_of_correct_bracketing_entail_wit_5_2 : correct_bracketing_entail_wit_5_2.
Axiom proof_of_correct_bracketing_entail_wit_6 : correct_bracketing_entail_wit_6.
Axiom proof_of_correct_bracketing_entail_wit_7 : correct_bracketing_entail_wit_7.
Axiom proof_of_correct_bracketing_return_wit_1 : correct_bracketing_return_wit_1.
Axiom proof_of_correct_bracketing_return_wit_2 : correct_bracketing_return_wit_2.
Axiom proof_of_correct_bracketing_return_wit_3 : correct_bracketing_return_wit_3.
Axiom proof_of_correct_bracketing_partial_solve_wit_1_pure : correct_bracketing_partial_solve_wit_1_pure.
Axiom proof_of_correct_bracketing_partial_solve_wit_1 : correct_bracketing_partial_solve_wit_1.

End VC_Correct.
