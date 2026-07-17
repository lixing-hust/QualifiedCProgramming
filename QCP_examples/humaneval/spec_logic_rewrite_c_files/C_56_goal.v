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
Require Import coins_56.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function correct_bracketing -----*)

Definition correct_bracketing_safety_wit_1 := 
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (PreH1 : (brackets_pre = brackets0)) (PreH2 : (valid_string input_l )) (PreH3 : (problem_56_pre_z input_l )) (PreH4 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "level" ) )) # Int  |->_)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  (store_string brackets_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_2 := 
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (brackets_pre = brackets0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_56_pre_z input_l )) (PreH6 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (store_string brackets_pre input_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_3 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input_l)))) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= level)) (PreH6 : (level <= i)) (PreH7 : (valid_string input_l )) (PreH8 : (problem_56_pre_z input_l )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH10 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (60 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 60) ”
.

Definition correct_bracketing_safety_wit_4 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ ((level + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level + 1 )) ”
.

Definition correct_bracketing_safety_wit_5 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition correct_bracketing_safety_wit_6 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
  **  (store_string brackets0 input_l )
|--
  “ (62 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 62) ”
.

Definition correct_bracketing_safety_wit_7 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (62 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 62) ”
.

Definition correct_bracketing_safety_wit_8 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH2 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
  **  (store_string brackets0 input_l )
|--
  “ False ”
.

Definition correct_bracketing_safety_wit_9 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ ((level - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level - 1 )) ”
.

Definition correct_bracketing_safety_wit_10 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition correct_bracketing_safety_wit_11 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  (store_string brackets0 input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_12 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH2 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
  **  (store_string brackets0 input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_13 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_14 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((level + 1 ) < 0)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH3 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (valid_string input_l )) (PreH11 : (problem_56_pre_z input_l )) (PreH12 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH13 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
  **  (store_string brackets0 input_l )
|--
  “ False ”
.

Definition correct_bracketing_safety_wit_15 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (level < 0)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (valid_string input_l )) (PreH11 : (problem_56_pre_z input_l )) (PreH12 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH13 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ False ”
.

Definition correct_bracketing_safety_wit_16 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((level - 1 ) < 0)) (PreH2 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (valid_string input_l )) (PreH11 : (problem_56_pre_z input_l )) (PreH12 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH13 : (bracket_state_56 input_l i level )) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input_l)) 0))
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  (store_string brackets0 input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_17 := 
forall (brackets0: Z) (input_l: (@list Z)) (n: Z) (i: Z) (level: Z) (PreH1 : (n = (string_length (input_l)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= level)) (PreH5 : (level <= (i + 1 ))) (PreH6 : (valid_string input_l )) (PreH7 : (problem_56_pre_z input_l )) (PreH8 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH9 : (bracket_state_56 input_l (i + 1 ) level )) ,
  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition correct_bracketing_safety_wit_18 := 
forall (brackets0: Z) (input_l: (@list Z)) (n: Z) (i: Z) (level: Z) (PreH1 : (n = (string_length (input_l)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= level)) (PreH5 : (level <= (i + 1 ))) (PreH6 : (valid_string input_l )) (PreH7 : (problem_56_pre_z input_l )) (PreH8 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH9 : (bracket_state_56 input_l (i + 1 ) level )) ,
  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition correct_bracketing_safety_wit_19 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input_l)))) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (0 <= level)) (PreH6 : (level <= i)) (PreH7 : (valid_string input_l )) (PreH8 : (problem_56_pre_z input_l )) (PreH9 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH10 : (bracket_state_56 input_l i level )) ,
  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_20 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (level <> 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition correct_bracketing_safety_wit_21 := 
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (level = 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (store_string brackets0 input_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition correct_bracketing_entail_wit_1 := 
(
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (brackets_pre = brackets0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_56_pre_z input_l )) (PreH6 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string brackets_pre input_l )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
|--
  “ (retval = (string_length (input_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_56_pre_z input_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ” 
  &&  “ (bracket_state_56 input_l 0 0 ) ”
  &&  ((( &( "brackets" ) )) # Ptr  |-> brackets0)
  **  (store_string brackets0 input_l )
) \/
(
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (brackets_pre = brackets0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_56_pre_z input_l )) (PreH6 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full brackets_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
|--
  “ (bracket_state_56 input_l 0 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.full brackets0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
).

Definition correct_bracketing_entail_wit_1_split_goal_1 := 
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (brackets_pre = brackets0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_56_pre_z input_l )) (PreH6 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full brackets_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
|--
  “ (bracket_state_56 input_l 0 0 ) ”
.

Definition correct_bracketing_entail_wit_1_split_goal_2 := 
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (brackets_pre = brackets0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_56_pre_z input_l )) (PreH6 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full brackets_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
|--
  “ (0 <= retval) ”
.

Definition correct_bracketing_entail_wit_1_split_goal_spatial := 
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input_l)))) (PreH2 : (0 <= ((string_length (input_l)) + 1 ))) (PreH3 : (brackets_pre = brackets0)) (PreH4 : (valid_string input_l )) (PreH5 : (problem_56_pre_z input_l )) (PreH6 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full brackets_pre ((string_length (input_l)) + 1 ) (c_string (input_l)) )
|--
  (CharArray.full brackets0 ((string_length (input_l)) + 1 ) (c_string (input_l)) )
.

Definition correct_bracketing_entail_wit_2_1 := 
(
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (level >= 0)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (valid_string input_l )) (PreH11 : (problem_56_pre_z input_l )) (PreH12 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH13 : (bracket_state_56 input_l i level )) ,
  (store_string brackets0 input_l )
|--
  “ (n = (string_length (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_56_pre_z input_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ” 
  &&  “ (bracket_state_56 input_l (i + 1 ) level ) ”
  &&  (store_string brackets0 input_l )
) \/
(
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : (level >= 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_56 input_l (i + 1 ) level ) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_2_1_split_goal_1 := 
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : (level >= 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_56 input_l (i + 1 ) level ) ”
.

Definition correct_bracketing_entail_wit_2_2 := 
(
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((level + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH3 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (valid_string input_l )) (PreH11 : (problem_56_pre_z input_l )) (PreH12 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH13 : (bracket_state_56 input_l i level )) ,
  (store_string brackets0 input_l )
|--
  “ (n = (string_length (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_56_pre_z input_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ” 
  &&  “ (bracket_state_56 input_l (i + 1 ) (level + 1 ) ) ”
  &&  (store_string brackets0 input_l )
) \/
(
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : ((level + 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_56 input_l (i + 1 ) (level + 1 ) ) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_2_2_split_goal_1 := 
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : ((level + 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) = 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_56 input_l (i + 1 ) (level + 1 ) ) ”
.

Definition correct_bracketing_entail_wit_2_3 := 
(
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((level - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (valid_string input_l )) (PreH11 : (problem_56_pre_z input_l )) (PreH12 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH13 : (bracket_state_56 input_l i level )) ,
  (store_string brackets0 input_l )
|--
  “ (n = (string_length (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (level - 1 )) ” 
  &&  “ ((level - 1 ) <= (i + 1 )) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_56_pre_z input_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ” 
  &&  “ (bracket_state_56 input_l (i + 1 ) (level - 1 ) ) ”
  &&  (store_string brackets0 input_l )
) \/
(
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : ((level - 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_56 input_l (i + 1 ) (level - 1 ) ) ”
  &&  emp
).

Definition correct_bracketing_entail_wit_2_3_split_goal_1 := 
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : ((level - 1 ) >= 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (bracket_state_56 input_l (i + 1 ) (level - 1 ) ) ”
.

Definition correct_bracketing_entail_wit_3 := 
forall (brackets0: Z) (input_l: (@list Z)) (n: Z) (i: Z) (level: Z) (PreH1 : (n = (string_length (input_l)))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (0 <= level)) (PreH5 : (level <= (i + 1 ))) (PreH6 : (valid_string input_l )) (PreH7 : (problem_56_pre_z input_l )) (PreH8 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH9 : (bracket_state_56 input_l (i + 1 ) level )) ,
  (store_string brackets0 input_l )
|--
  “ (n = (string_length (input_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_56_pre_z input_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ” 
  &&  “ (bracket_state_56 input_l (i + 1 ) level ) ”
  &&  (store_string brackets0 input_l )
.

Definition correct_bracketing_return_wit_1 := 
(
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (level = 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  (store_string brackets0 input_l )
|--
  “ (problem_56_spec_z input_l 1 ) ”
  &&  (store_string brackets0 input_l )
) \/
(
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : (level = 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (problem_56_spec_z input_l 1 ) ”
  &&  emp
).

Definition correct_bracketing_return_wit_1_split_goal_1 := 
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : (level = 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (problem_56_spec_z input_l 1 ) ”
.

Definition correct_bracketing_return_wit_2 := 
(
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (level <> 0)) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input_l)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (0 <= level)) (PreH7 : (level <= i)) (PreH8 : (valid_string input_l )) (PreH9 : (problem_56_pre_z input_l )) (PreH10 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH11 : (bracket_state_56 input_l i level )) ,
  (store_string brackets0 input_l )
|--
  “ (problem_56_spec_z input_l 0 ) ”
  &&  (store_string brackets0 input_l )
) \/
(
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : (level <> 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (problem_56_spec_z input_l 0 ) ”
  &&  emp
).

Definition correct_bracketing_return_wit_2_split_goal_1 := 
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : (level <> 0)) (PreH3 : (i >= n)) (PreH4 : (n = (string_length (input_l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (0 <= level)) (PreH8 : (level <= i)) (PreH9 : (valid_string input_l )) (PreH10 : (problem_56_pre_z input_l )) (PreH11 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH12 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (problem_56_spec_z input_l 0 ) ”
.

Definition correct_bracketing_return_wit_3 := 
(
forall (brackets0: Z) (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : ((level - 1 ) < 0)) (PreH2 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH3 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= level)) (PreH9 : (level <= i)) (PreH10 : (valid_string input_l )) (PreH11 : (problem_56_pre_z input_l )) (PreH12 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH13 : (bracket_state_56 input_l i level )) ,
  (store_string brackets0 input_l )
|--
  “ (problem_56_spec_z input_l 0 ) ”
  &&  (store_string brackets0 input_l )
) \/
(
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : ((level - 1 ) < 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (problem_56_spec_z input_l 0 ) ”
  &&  emp
).

Definition correct_bracketing_return_wit_3_split_goal_1 := 
forall (input_l: (@list Z)) (level: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input_l)) + 1 ))) (PreH2 : ((level - 1 ) < 0)) (PreH3 : ((Znth i (c_string (input_l)) 0) = 62)) (PreH4 : ((Znth i (c_string (input_l)) 0) <> 60)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= level)) (PreH10 : (level <= i)) (PreH11 : (valid_string input_l )) (PreH12 : (problem_56_pre_z input_l )) (PreH13 : (((string_length (input_l)) + 1 ) < INT_MAX)) (PreH14 : (bracket_state_56 input_l i level )) ,
  TT && emp 
|--
  “ (problem_56_spec_z input_l 0 ) ”
.

Definition correct_bracketing_partial_solve_wit_1_pure := 
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (PreH1 : (brackets_pre = brackets0)) (PreH2 : (valid_string input_l )) (PreH3 : (problem_56_pre_z input_l )) (PreH4 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  (store_string brackets_pre input_l )
|--
  “ (valid_string input_l ) ” 
  &&  “ ((string_length (input_l)) < INT_MAX) ”
.

Definition correct_bracketing_partial_solve_wit_1_aux := 
forall (brackets_pre: Z) (brackets0: Z) (input_l: (@list Z)) (PreH1 : (brackets_pre = brackets0)) (PreH2 : (valid_string input_l )) (PreH3 : (problem_56_pre_z input_l )) (PreH4 : (((string_length (input_l)) + 1 ) < INT_MAX)) ,
  (store_string brackets_pre input_l )
|--
  “ (valid_string input_l ) ” 
  &&  “ ((string_length (input_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input_l)) + 1 )) ” 
  &&  “ (brackets_pre = brackets0) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (problem_56_pre_z input_l ) ” 
  &&  “ (((string_length (input_l)) + 1 ) < INT_MAX) ”
  &&  (store_string brackets_pre input_l )
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
Axiom proof_of_correct_bracketing_safety_wit_16 : correct_bracketing_safety_wit_16.
Axiom proof_of_correct_bracketing_safety_wit_17 : correct_bracketing_safety_wit_17.
Axiom proof_of_correct_bracketing_safety_wit_18 : correct_bracketing_safety_wit_18.
Axiom proof_of_correct_bracketing_safety_wit_19 : correct_bracketing_safety_wit_19.
Axiom proof_of_correct_bracketing_safety_wit_20 : correct_bracketing_safety_wit_20.
Axiom proof_of_correct_bracketing_safety_wit_21 : correct_bracketing_safety_wit_21.
Axiom proof_of_correct_bracketing_entail_wit_1 : correct_bracketing_entail_wit_1.
Axiom proof_of_correct_bracketing_entail_wit_2_1 : correct_bracketing_entail_wit_2_1.
Axiom proof_of_correct_bracketing_entail_wit_2_2 : correct_bracketing_entail_wit_2_2.
Axiom proof_of_correct_bracketing_entail_wit_2_3 : correct_bracketing_entail_wit_2_3.
Axiom proof_of_correct_bracketing_entail_wit_3 : correct_bracketing_entail_wit_3.
Axiom proof_of_correct_bracketing_return_wit_1 : correct_bracketing_return_wit_1.
Axiom proof_of_correct_bracketing_return_wit_2 : correct_bracketing_return_wit_2.
Axiom proof_of_correct_bracketing_return_wit_3 : correct_bracketing_return_wit_3.
Axiom proof_of_correct_bracketing_partial_solve_wit_1_pure : correct_bracketing_partial_solve_wit_1_pure.
Axiom proof_of_correct_bracketing_partial_solve_wit_1 : correct_bracketing_partial_solve_wit_1.

End VC_Correct.
