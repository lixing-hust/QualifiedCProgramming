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
Require Import coins_119.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function match_parens -----*)

Definition match_parens_safety_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (l2)))) (PreH2 : (retval = (string_length (l1)))) (PreH3 : (0 <= ((string_length (l2)) + 1 ))) (PreH4 : (0 <= ((string_length (l1)) + 1 ))) (PreH5 : (valid_string l1 )) (PreH6 : (valid_string l2 )) (PreH7 : (problem_119_pre_z l1 l2 )) (PreH8 : (paren_codes_119 l1 )) (PreH9 : (paren_codes_119 l2 )) (PreH10 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string s2_pre l2 )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (l2)))) (PreH2 : (retval = (string_length (l1)))) (PreH3 : (0 <= ((string_length (l2)) + 1 ))) (PreH4 : (0 <= ((string_length (l1)) + 1 ))) (PreH5 : (valid_string l1 )) (PreH6 : (valid_string l2 )) (PreH7 : (problem_119_pre_z l1 l2 )) (PreH8 : (paren_codes_119 l1 )) (PreH9 : (paren_codes_119 l2 )) (PreH10 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string s2_pre l2 )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (l2)))) (PreH2 : (retval = (string_length (l1)))) (PreH3 : (0 <= ((string_length (l2)) + 1 ))) (PreH4 : (0 <= ((string_length (l1)) + 1 ))) (PreH5 : (valid_string l1 )) (PreH6 : (valid_string l2 )) (PreH7 : (problem_119_pre_z l1 l2 )) (PreH8 : (paren_codes_119 l1 )) (PreH9 : (paren_codes_119 l2 )) (PreH10 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  ((( &( "can" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string s2_pre l2 )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (l2)))) (PreH2 : (retval = (string_length (l1)))) (PreH3 : (0 <= ((string_length (l2)) + 1 ))) (PreH4 : (0 <= ((string_length (l1)) + 1 ))) (PreH5 : (valid_string l1 )) (PreH6 : (valid_string l2 )) (PreH7 : (problem_119_pre_z l1 l2 )) (PreH8 : (paren_codes_119 l1 )) (PreH9 : (paren_codes_119 l2 )) (PreH10 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  ((( &( "can" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string s2_pre l2 )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_5 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_6 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_7 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_8 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_9 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_10 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_11 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_12 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_13 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_14 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_15 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_16 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_17 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_18 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_19 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_20 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_21 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_22 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_23 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_24 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_25 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_26 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_27 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_28 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_29 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-(n1 + i )) <= count)) (PreH7 : (count <= (n1 + i ))) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_30 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-(n1 + i )) <= count)) (PreH7 : (count <= (n1 + i ))) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_31 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_32 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_33 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_34 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_35 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_36 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_37 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_38 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_39 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_40 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_41 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_42 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_43 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_44 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_45 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_46 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_47 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_48 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_49 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_50 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_51 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-(n1 + i )) <= count)) (PreH7 : (count <= (n1 + i ))) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_52 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-(n1 + i )) <= count)) (PreH7 : (count <= (n1 + i ))) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_53 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1_addr_v: Z) (n2_addr_v: Z) (i_addr_v: Z) (ch_addr_v: Z) (count_addr_v: Z) (can_addr_v: Z) (PreH1 : (problem_119_spec_z l1 l2 0 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1_addr_v)
  **  ((( &( "n2" ) )) # Int  |-> n2_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  ((( &( "count" ) )) # Int  |-> count_addr_v)
  **  ((( &( "can" ) )) # Int  |-> can_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_54 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (count = 0)) (PreH2 : (i >= n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_55 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (count = 0)) (PreH2 : (i >= n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_56 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can <> 1)) (PreH2 : (count = 0)) (PreH3 : (i >= n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ False ”
.

Definition match_parens_safety_wit_57 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can = 1)) (PreH2 : (count = 0)) (PreH3 : (i >= n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ False ”
.

Definition match_parens_safety_wit_58 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1_addr_v: Z) (n2_addr_v: Z) (i_addr_v: Z) (ch_addr_v: Z) (count_addr_v: Z) (can_addr_v: Z) (PreH1 : (problem_119_spec_z l1 l2 1 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1_addr_v)
  **  ((( &( "n2" ) )) # Int  |-> n2_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  ((( &( "count" ) )) # Int  |-> count_addr_v)
  **  ((( &( "can" ) )) # Int  |-> can_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_59 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can <> 1)) (PreH2 : (count = 0)) (PreH3 : (i >= n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_60 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can <> 1)) (PreH2 : (count = 0)) (PreH3 : (i >= n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_61 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can <> 1)) (PreH2 : (count = 0)) (PreH3 : (i >= n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "can" ) )) # Int  |-> 1)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_62 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_63 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_64 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_65 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_66 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_67 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_68 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_69 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_70 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_71 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_72 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_73 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) = 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_74 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_75 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH2 : (i < n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-i) <= count)) (PreH8 : (count <= i)) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_76 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_77 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_78 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_79 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l2)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_80 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_81 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_82 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_83 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_84 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_85 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_86 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-(n2 + i )) <= count)) (PreH7 : (count <= (n2 + i ))) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_87 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i < n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-(n2 + i )) <= count)) (PreH7 : (count <= (n2 + i ))) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition match_parens_safety_wit_88 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_89 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_90 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition match_parens_safety_wit_91 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_92 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_93 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_94 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count - 1 )) ”
.

Definition match_parens_safety_wit_95 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_96 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_97 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) = 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_98 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_99 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH2 : (i < n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_100 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_101 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_102 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_103 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (l1)) 0))
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_safety_wit_104 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_105 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_106 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_107 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_parens_safety_wit_108 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-(n2 + i )) <= count)) (PreH7 : (count <= (n2 + i ))) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_109 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-(n2 + i )) <= count)) (PreH7 : (count <= (n2 + i ))) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_110 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can = 1)) (PreH2 : (i >= n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ False ”
.

Definition match_parens_safety_wit_111 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can <> 1)) (PreH2 : (i >= n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ False ”
.

Definition match_parens_safety_wit_112 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1_addr_v: Z) (n2_addr_v: Z) (i_addr_v: Z) (ch_addr_v: Z) (count_addr_v: Z) (can_addr_v: Z) (PreH1 : (problem_119_spec_z l1 l2 1 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1_addr_v)
  **  ((( &( "n2" ) )) # Int  |-> n2_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  ((( &( "count" ) )) # Int  |-> count_addr_v)
  **  ((( &( "can" ) )) # Int  |-> can_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_parens_safety_wit_113 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1_addr_v: Z) (n2_addr_v: Z) (i_addr_v: Z) (ch_addr_v: Z) (count_addr_v: Z) (can_addr_v: Z) (PreH1 : (problem_119_spec_z l1 l2 0 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> n1_addr_v)
  **  ((( &( "n2" ) )) # Int  |-> n2_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  ((( &( "count" ) )) # Int  |-> count_addr_v)
  **  ((( &( "can" ) )) # Int  |-> can_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_parens_entail_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (l2)))) (PreH2 : (retval = (string_length (l1)))) (PreH3 : (0 <= ((string_length (l2)) + 1 ))) (PreH4 : (0 <= ((string_length (l1)) + 1 ))) (PreH5 : (valid_string l1 )) (PreH6 : (valid_string l2 )) (PreH7 : (problem_119_pre_z l1 l2 )) (PreH8 : (paren_codes_119 l1 )) (PreH9 : (paren_codes_119 l2 )) (PreH10 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  (store_string s2_pre l2 )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
|--
  (“ (retval = (string_length (l1))) ” 
  &&  “ (retval_2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((-0) <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) 0 0 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (retval = (string_length (l1))) ” 
  &&  “ (retval_2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((-0) <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) 0 0 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_5 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_6 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_7 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_2_8 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_3_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_3_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_3_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_3_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_4_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n2) ” 
  &&  “ ((-(n1 + 0 )) <= count) ” 
  &&  “ (count <= (n1 + 0 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n2) ” 
  &&  “ ((-(n1 + 0 )) <= count) ” 
  &&  “ (count <= (n1 + 0 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_4_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n1)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n1)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n2) ” 
  &&  “ ((-(n1 + 0 )) <= count) ” 
  &&  “ (count <= (n1 + 0 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n2) ” 
  &&  “ ((-(n1 + 0 )) <= count) ” 
  &&  “ (count <= (n1 + 0 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_5 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_6 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_7 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_5_8 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-((n1 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n1 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_6_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_6_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_6_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_6_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-((n1 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n1 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) ((n1 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(n1 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n1 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_7_1 := 
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (count <> 0)) (PreH2 : (i >= n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
) \/
(
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (count <> 0)) (PreH4 : (i >= n2)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n2)) (PreH9 : ((-(n1 + i )) <= count)) (PreH10 : (count <= (n1 + i ))) (PreH11 : (can = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  emp
).

Definition match_parens_entail_wit_7_1_split_goal_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (count <> 0)) (PreH4 : (i >= n2)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n2)) (PreH9 : ((-(n1 + i )) <= count)) (PreH10 : (count <= (n1 + i ))) (PreH11 : (can = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
.

Definition match_parens_entail_wit_7_2 := 
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (count <> 0)) (PreH2 : (i >= n2)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n2)) (PreH7 : ((-(n1 + i )) <= count)) (PreH8 : (count <= (n1 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
) \/
(
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (count <> 0)) (PreH4 : (i >= n2)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n2)) (PreH9 : ((-(n1 + i )) <= count)) (PreH10 : (count <= (n1 + i ))) (PreH11 : (can = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  emp
).

Definition match_parens_entail_wit_7_2_split_goal_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (count <> 0)) (PreH4 : (i >= n2)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n2)) (PreH9 : ((-(n1 + i )) <= count)) (PreH10 : (count <= (n1 + i ))) (PreH11 : (can = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
.

Definition match_parens_entail_wit_8 := 
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can = 1)) (PreH2 : (count = 0)) (PreH3 : (i >= n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
) \/
(
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (can = 1)) (PreH4 : (count = 0)) (PreH5 : (i >= n2)) (PreH6 : (n1 = (string_length (l1)))) (PreH7 : (n2 = (string_length (l2)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n2)) (PreH10 : ((-(n1 + i )) <= count)) (PreH11 : (count <= (n1 + i ))) (PreH12 : (can = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string l1 )) (PreH16 : (valid_string l2 )) (PreH17 : (problem_119_pre_z l1 l2 )) (PreH18 : (paren_codes_119 l1 )) (PreH19 : (paren_codes_119 l2 )) (PreH20 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH21 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
  &&  emp
).

Definition match_parens_entail_wit_8_split_goal_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (can = 1)) (PreH4 : (count = 0)) (PreH5 : (i >= n2)) (PreH6 : (n1 = (string_length (l1)))) (PreH7 : (n2 = (string_length (l2)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n2)) (PreH10 : ((-(n1 + i )) <= count)) (PreH11 : (count <= (n1 + i ))) (PreH12 : (can = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string l1 )) (PreH16 : (valid_string l2 )) (PreH17 : (problem_119_pre_z l1 l2 )) (PreH18 : (paren_codes_119 l1 )) (PreH19 : (paren_codes_119 l2 )) (PreH20 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH21 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
.

Definition match_parens_entail_wit_9 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can <> 1)) (PreH2 : (count = 0)) (PreH3 : (i >= n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-(n1 + i )) <= count)) (PreH9 : (count <= (n1 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n2) ” 
  &&  “ ((-0) <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1 = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) 0 0 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n2) ” 
  &&  “ ((-0) <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) 0 0 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_5 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_6 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) <> 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_7 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_10_8 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l2)) 0) = 40)) (PreH3 : (i < n2)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n2)) (PreH8 : ((-i) <= count)) (PreH9 : (count <= i)) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n2) ” 
  &&  “ ((-(i + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l2)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_11_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_11_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_11_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_11_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n2)) (PreH5 : ((-(i + 1 )) <= count)) (PreH6 : (count <= (i + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n2) ” 
  &&  “ ((-(i + 1 )) <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (i + 1 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_12_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n1) ” 
  &&  “ ((-(n2 + 0 )) <= count) ” 
  &&  “ (count <= (n2 + 0 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n1) ” 
  &&  “ ((-(n2 + 0 )) <= count) ” 
  &&  “ (count <= (n2 + 0 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_12_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (i >= n2)) (PreH2 : (n1 = (string_length (l1)))) (PreH3 : (n2 = (string_length (l2)))) (PreH4 : (0 <= i)) (PreH5 : (i <= n2)) (PreH6 : ((-i) <= count)) (PreH7 : (count <= i)) (PreH8 : (can = 1)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (valid_string l1 )) (PreH12 : (valid_string l2 )) (PreH13 : (problem_119_pre_z l1 l2 )) (PreH14 : (paren_codes_119 l1 )) (PreH15 : (paren_codes_119 l2 )) (PreH16 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH17 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH18 : (paren_scan_state_119 (app (l2) (l1)) i count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n1) ” 
  &&  “ ((-(n2 + 0 )) <= count) ” 
  &&  “ (count <= (n2 + 0 )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n1) ” 
  &&  “ ((-(n2 + 0 )) <= count) ” 
  &&  “ (count <= (n2 + 0 )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + 0 ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) >= 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (can = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_5 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_6 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count - 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) <> 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count - 1 )) ” 
  &&  “ ((count - 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count - 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_7 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_13_8 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : ((count + 1 ) < 0)) (PreH2 : ((Znth i (c_string (l1)) 0) = 40)) (PreH3 : (i < n1)) (PreH4 : (n1 = (string_length (l1)))) (PreH5 : (n2 = (string_length (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n1)) (PreH8 : ((-(n2 + i )) <= count)) (PreH9 : (count <= (n2 + i ))) (PreH10 : (can = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string l1 )) (PreH14 : (valid_string l2 )) (PreH15 : (problem_119_pre_z l1 l2 )) (PreH16 : (paren_codes_119 l1 )) (PreH17 : (paren_codes_119 l2 )) (PreH18 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH19 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH20 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 40) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n1) ” 
  &&  “ ((-((n2 + i ) + 1 )) <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= ((n2 + i ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Znth i (c_string (l1)) 0) = 41) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) (count + 1 ) 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_14_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_14_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 1)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_14_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 40)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_14_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (n1: Z) (n2: Z) (i: Z) (count: Z) (can: Z) (ch: Z) (PreH1 : (n1 = (string_length (l1)))) (PreH2 : (n2 = (string_length (l2)))) (PreH3 : (0 <= i)) (PreH4 : (i < n1)) (PreH5 : ((-((n2 + i ) + 1 )) <= count)) (PreH6 : (count <= ((n2 + i ) + 1 ))) (PreH7 : (can = 0)) (PreH8 : (ch = 41)) (PreH9 : (valid_string l1 )) (PreH10 : (valid_string l2 )) (PreH11 : (problem_119_pre_z l1 l2 )) (PreH12 : (paren_codes_119 l1 )) (PreH13 : (paren_codes_119 l2 )) (PreH14 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH15 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH16 : (paren_scan_state_119 (app (l2) (l1)) ((n2 + i ) + 1 ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
  ||
  (“ (n1 = (string_length (l1))) ” 
  &&  “ (n2 = (string_length (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((-(n2 + (i + 1 ) )) <= count) ” 
  &&  “ (count <= (n2 + (i + 1 ) )) ” 
  &&  “ (can = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ” 
  &&  “ (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 ) ” 
  &&  “ (paren_scan_state_119 (app (l2) (l1)) (n2 + (i + 1 ) ) count can ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 ))
.

Definition match_parens_entail_wit_15 := 
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can = 1)) (PreH2 : (i >= n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 1)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
) \/
(
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (can = 1)) (PreH4 : (i >= n1)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n1)) (PreH9 : ((-(n2 + i )) <= count)) (PreH10 : (count <= (n2 + i ))) (PreH11 : (can = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH21 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
  &&  emp
).

Definition match_parens_entail_wit_15_split_goal_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (can = 1)) (PreH4 : (i >= n1)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n1)) (PreH9 : ((-(n2 + i )) <= count)) (PreH10 : (count <= (n2 + i ))) (PreH11 : (can = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH21 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
.

Definition match_parens_entail_wit_16 := 
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (can <> 1)) (PreH2 : (i >= n1)) (PreH3 : (n1 = (string_length (l1)))) (PreH4 : (n2 = (string_length (l2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n1)) (PreH7 : ((-(n2 + i )) <= count)) (PreH8 : (count <= (n2 + i ))) (PreH9 : (can = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (valid_string l1 )) (PreH13 : (valid_string l2 )) (PreH14 : (problem_119_pre_z l1 l2 )) (PreH15 : (paren_codes_119 l1 )) (PreH16 : (paren_codes_119 l2 )) (PreH17 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH18 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH19 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
) \/
(
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (can <> 1)) (PreH4 : (i >= n1)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n1)) (PreH9 : ((-(n2 + i )) <= count)) (PreH10 : (count <= (n2 + i ))) (PreH11 : (can = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH21 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  emp
).

Definition match_parens_entail_wit_16_split_goal_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (ch: Z) (can: Z) (count: Z) (i: Z) (n2: Z) (n1: Z) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (can <> 1)) (PreH4 : (i >= n1)) (PreH5 : (n1 = (string_length (l1)))) (PreH6 : (n2 = (string_length (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n1)) (PreH9 : ((-(n2 + i )) <= count)) (PreH10 : (count <= (n2 + i ))) (PreH11 : (can = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string l1 )) (PreH15 : (valid_string l2 )) (PreH16 : (problem_119_pre_z l1 l2 )) (PreH17 : (paren_codes_119 l1 )) (PreH18 : (paren_codes_119 l2 )) (PreH19 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) (PreH20 : (paren_scan_state_119 (app (l1) (l2)) (n1 + n2 ) 0 0 )) (PreH21 : (paren_scan_state_119 (app (l2) (l1)) (n2 + i ) count can )) ,
  TT && emp 
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
.

Definition match_parens_return_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (problem_119_spec_z l1 l2 0 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
.

Definition match_parens_return_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (problem_119_spec_z l1 l2 1 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
.

Definition match_parens_return_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (problem_119_spec_z l1 l2 1 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 1 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
.

Definition match_parens_return_wit_4 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (problem_119_spec_z l1 l2 0 )) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (problem_119_spec_z l1 l2 0 ) ”
  &&  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
.

Definition match_parens_partial_solve_wit_1_pure := 
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (valid_string l1 )) (PreH2 : (valid_string l2 )) (PreH3 : (problem_119_pre_z l1 l2 )) (PreH4 : (paren_codes_119 l1 )) (PreH5 : (paren_codes_119 l2 )) (PreH6 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (valid_string l1 ) ” 
  &&  “ ((string_length (l1)) < INT_MAX) ”
) \/
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (valid_string l1 )) (PreH4 : (valid_string l2 )) (PreH5 : (problem_119_pre_z l1 l2 )) (PreH6 : (paren_codes_119 l1 )) (PreH7 : (paren_codes_119 l2 )) (PreH8 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  (CharArray.full s2_pre ((string_length (l2)) + 1 ) (c_string (l2)) )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ ((string_length (l1)) < INT_MAX) ”
).

Definition match_parens_partial_solve_wit_1_pure_split_goal_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= ((string_length (l2)) + 1 ))) (PreH2 : (0 <= ((string_length (l1)) + 1 ))) (PreH3 : (valid_string l1 )) (PreH4 : (valid_string l2 )) (PreH5 : (problem_119_pre_z l1 l2 )) (PreH6 : (paren_codes_119 l1 )) (PreH7 : (paren_codes_119 l2 )) (PreH8 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  (CharArray.full s2_pre ((string_length (l2)) + 1 ) (c_string (l2)) )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ ((string_length (l1)) < INT_MAX) ”
.

Definition match_parens_partial_solve_wit_1_aux := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (valid_string l1 )) (PreH2 : (valid_string l2 )) (PreH3 : (problem_119_pre_z l1 l2 )) (PreH4 : (paren_codes_119 l1 )) (PreH5 : (paren_codes_119 l2 )) (PreH6 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  (store_string s1_pre l1 )
  **  (store_string s2_pre l2 )
|--
  “ (valid_string l1 ) ” 
  &&  “ ((string_length (l1)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (l2)) + 1 )) ” 
  &&  “ (0 <= ((string_length (l1)) + 1 )) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ”
  &&  (store_string s1_pre l1 )
  **  (CharArray.full s2_pre ((string_length (l2)) + 1 ) (c_string (l2)) )
.

Definition match_parens_partial_solve_wit_1 := match_parens_partial_solve_wit_1_pure -> match_parens_partial_solve_wit_1_aux.

Definition match_parens_partial_solve_wit_2_pure := 
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l1)))) (PreH2 : (0 <= ((string_length (l2)) + 1 ))) (PreH3 : (0 <= ((string_length (l1)) + 1 ))) (PreH4 : (valid_string l1 )) (PreH5 : (valid_string l2 )) (PreH6 : (problem_119_pre_z l1 l2 )) (PreH7 : (paren_codes_119 l1 )) (PreH8 : (paren_codes_119 l2 )) (PreH9 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  ((( &( "n2" ) )) # Int  |->_)
  **  (store_string s1_pre l1 )
  **  (CharArray.full s2_pre ((string_length (l2)) + 1 ) (c_string (l2)) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (valid_string l2 ) ” 
  &&  “ ((string_length (l2)) < INT_MAX) ”
) \/
(
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (l1)))) (PreH4 : (0 <= ((string_length (l2)) + 1 ))) (PreH5 : (0 <= ((string_length (l1)) + 1 ))) (PreH6 : (valid_string l1 )) (PreH7 : (valid_string l2 )) (PreH8 : (problem_119_pre_z l1 l2 )) (PreH9 : (paren_codes_119 l1 )) (PreH10 : (paren_codes_119 l2 )) (PreH11 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n2" ) )) # Int  |->_)
  **  (CharArray.full s2_pre ((string_length (l2)) + 1 ) (c_string (l2)) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ ((string_length (l2)) < INT_MAX) ”
).

Definition match_parens_partial_solve_wit_2_pure_split_goal_1 := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (l1)))) (PreH4 : (0 <= ((string_length (l2)) + 1 ))) (PreH5 : (0 <= ((string_length (l1)) + 1 ))) (PreH6 : (valid_string l1 )) (PreH7 : (valid_string l2 )) (PreH8 : (problem_119_pre_z l1 l2 )) (PreH9 : (paren_codes_119 l1 )) (PreH10 : (paren_codes_119 l2 )) (PreH11 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
  **  ((( &( "n2" ) )) # Int  |->_)
  **  (CharArray.full s2_pre ((string_length (l2)) + 1 ) (c_string (l2)) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ ((string_length (l2)) < INT_MAX) ”
.

Definition match_parens_partial_solve_wit_2_aux := 
forall (s2_pre: Z) (s1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l1)))) (PreH2 : (0 <= ((string_length (l2)) + 1 ))) (PreH3 : (0 <= ((string_length (l1)) + 1 ))) (PreH4 : (valid_string l1 )) (PreH5 : (valid_string l2 )) (PreH6 : (problem_119_pre_z l1 l2 )) (PreH7 : (paren_codes_119 l1 )) (PreH8 : (paren_codes_119 l2 )) (PreH9 : (((string_length (l1)) + (string_length (l2)) ) < INT_MAX)) ,
  (store_string s1_pre l1 )
  **  (CharArray.full s2_pre ((string_length (l2)) + 1 ) (c_string (l2)) )
|--
  “ (valid_string l2 ) ” 
  &&  “ ((string_length (l2)) < INT_MAX) ” 
  &&  “ (retval = (string_length (l1))) ” 
  &&  “ (0 <= ((string_length (l2)) + 1 )) ” 
  &&  “ (0 <= ((string_length (l1)) + 1 )) ” 
  &&  “ (valid_string l1 ) ” 
  &&  “ (valid_string l2 ) ” 
  &&  “ (problem_119_pre_z l1 l2 ) ” 
  &&  “ (paren_codes_119 l1 ) ” 
  &&  “ (paren_codes_119 l2 ) ” 
  &&  “ (((string_length (l1)) + (string_length (l2)) ) < INT_MAX) ”
  &&  (store_string s2_pre l2 )
  **  (CharArray.full s1_pre ((string_length (l1)) + 1 ) (c_string (l1)) )
.

Definition match_parens_partial_solve_wit_2 := match_parens_partial_solve_wit_2_pure -> match_parens_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_match_parens_safety_wit_1 : match_parens_safety_wit_1.
Axiom proof_of_match_parens_safety_wit_2 : match_parens_safety_wit_2.
Axiom proof_of_match_parens_safety_wit_3 : match_parens_safety_wit_3.
Axiom proof_of_match_parens_safety_wit_4 : match_parens_safety_wit_4.
Axiom proof_of_match_parens_safety_wit_5 : match_parens_safety_wit_5.
Axiom proof_of_match_parens_safety_wit_6 : match_parens_safety_wit_6.
Axiom proof_of_match_parens_safety_wit_7 : match_parens_safety_wit_7.
Axiom proof_of_match_parens_safety_wit_8 : match_parens_safety_wit_8.
Axiom proof_of_match_parens_safety_wit_9 : match_parens_safety_wit_9.
Axiom proof_of_match_parens_safety_wit_10 : match_parens_safety_wit_10.
Axiom proof_of_match_parens_safety_wit_11 : match_parens_safety_wit_11.
Axiom proof_of_match_parens_safety_wit_12 : match_parens_safety_wit_12.
Axiom proof_of_match_parens_safety_wit_13 : match_parens_safety_wit_13.
Axiom proof_of_match_parens_safety_wit_14 : match_parens_safety_wit_14.
Axiom proof_of_match_parens_safety_wit_15 : match_parens_safety_wit_15.
Axiom proof_of_match_parens_safety_wit_16 : match_parens_safety_wit_16.
Axiom proof_of_match_parens_safety_wit_17 : match_parens_safety_wit_17.
Axiom proof_of_match_parens_safety_wit_18 : match_parens_safety_wit_18.
Axiom proof_of_match_parens_safety_wit_19 : match_parens_safety_wit_19.
Axiom proof_of_match_parens_safety_wit_20 : match_parens_safety_wit_20.
Axiom proof_of_match_parens_safety_wit_21 : match_parens_safety_wit_21.
Axiom proof_of_match_parens_safety_wit_22 : match_parens_safety_wit_22.
Axiom proof_of_match_parens_safety_wit_23 : match_parens_safety_wit_23.
Axiom proof_of_match_parens_safety_wit_24 : match_parens_safety_wit_24.
Axiom proof_of_match_parens_safety_wit_25 : match_parens_safety_wit_25.
Axiom proof_of_match_parens_safety_wit_26 : match_parens_safety_wit_26.
Axiom proof_of_match_parens_safety_wit_27 : match_parens_safety_wit_27.
Axiom proof_of_match_parens_safety_wit_28 : match_parens_safety_wit_28.
Axiom proof_of_match_parens_safety_wit_29 : match_parens_safety_wit_29.
Axiom proof_of_match_parens_safety_wit_30 : match_parens_safety_wit_30.
Axiom proof_of_match_parens_safety_wit_31 : match_parens_safety_wit_31.
Axiom proof_of_match_parens_safety_wit_32 : match_parens_safety_wit_32.
Axiom proof_of_match_parens_safety_wit_33 : match_parens_safety_wit_33.
Axiom proof_of_match_parens_safety_wit_34 : match_parens_safety_wit_34.
Axiom proof_of_match_parens_safety_wit_35 : match_parens_safety_wit_35.
Axiom proof_of_match_parens_safety_wit_36 : match_parens_safety_wit_36.
Axiom proof_of_match_parens_safety_wit_37 : match_parens_safety_wit_37.
Axiom proof_of_match_parens_safety_wit_38 : match_parens_safety_wit_38.
Axiom proof_of_match_parens_safety_wit_39 : match_parens_safety_wit_39.
Axiom proof_of_match_parens_safety_wit_40 : match_parens_safety_wit_40.
Axiom proof_of_match_parens_safety_wit_41 : match_parens_safety_wit_41.
Axiom proof_of_match_parens_safety_wit_42 : match_parens_safety_wit_42.
Axiom proof_of_match_parens_safety_wit_43 : match_parens_safety_wit_43.
Axiom proof_of_match_parens_safety_wit_44 : match_parens_safety_wit_44.
Axiom proof_of_match_parens_safety_wit_45 : match_parens_safety_wit_45.
Axiom proof_of_match_parens_safety_wit_46 : match_parens_safety_wit_46.
Axiom proof_of_match_parens_safety_wit_47 : match_parens_safety_wit_47.
Axiom proof_of_match_parens_safety_wit_48 : match_parens_safety_wit_48.
Axiom proof_of_match_parens_safety_wit_49 : match_parens_safety_wit_49.
Axiom proof_of_match_parens_safety_wit_50 : match_parens_safety_wit_50.
Axiom proof_of_match_parens_safety_wit_51 : match_parens_safety_wit_51.
Axiom proof_of_match_parens_safety_wit_52 : match_parens_safety_wit_52.
Axiom proof_of_match_parens_safety_wit_53 : match_parens_safety_wit_53.
Axiom proof_of_match_parens_safety_wit_54 : match_parens_safety_wit_54.
Axiom proof_of_match_parens_safety_wit_55 : match_parens_safety_wit_55.
Axiom proof_of_match_parens_safety_wit_56 : match_parens_safety_wit_56.
Axiom proof_of_match_parens_safety_wit_57 : match_parens_safety_wit_57.
Axiom proof_of_match_parens_safety_wit_58 : match_parens_safety_wit_58.
Axiom proof_of_match_parens_safety_wit_59 : match_parens_safety_wit_59.
Axiom proof_of_match_parens_safety_wit_60 : match_parens_safety_wit_60.
Axiom proof_of_match_parens_safety_wit_61 : match_parens_safety_wit_61.
Axiom proof_of_match_parens_safety_wit_62 : match_parens_safety_wit_62.
Axiom proof_of_match_parens_safety_wit_63 : match_parens_safety_wit_63.
Axiom proof_of_match_parens_safety_wit_64 : match_parens_safety_wit_64.
Axiom proof_of_match_parens_safety_wit_65 : match_parens_safety_wit_65.
Axiom proof_of_match_parens_safety_wit_66 : match_parens_safety_wit_66.
Axiom proof_of_match_parens_safety_wit_67 : match_parens_safety_wit_67.
Axiom proof_of_match_parens_safety_wit_68 : match_parens_safety_wit_68.
Axiom proof_of_match_parens_safety_wit_69 : match_parens_safety_wit_69.
Axiom proof_of_match_parens_safety_wit_70 : match_parens_safety_wit_70.
Axiom proof_of_match_parens_safety_wit_71 : match_parens_safety_wit_71.
Axiom proof_of_match_parens_safety_wit_72 : match_parens_safety_wit_72.
Axiom proof_of_match_parens_safety_wit_73 : match_parens_safety_wit_73.
Axiom proof_of_match_parens_safety_wit_74 : match_parens_safety_wit_74.
Axiom proof_of_match_parens_safety_wit_75 : match_parens_safety_wit_75.
Axiom proof_of_match_parens_safety_wit_76 : match_parens_safety_wit_76.
Axiom proof_of_match_parens_safety_wit_77 : match_parens_safety_wit_77.
Axiom proof_of_match_parens_safety_wit_78 : match_parens_safety_wit_78.
Axiom proof_of_match_parens_safety_wit_79 : match_parens_safety_wit_79.
Axiom proof_of_match_parens_safety_wit_80 : match_parens_safety_wit_80.
Axiom proof_of_match_parens_safety_wit_81 : match_parens_safety_wit_81.
Axiom proof_of_match_parens_safety_wit_82 : match_parens_safety_wit_82.
Axiom proof_of_match_parens_safety_wit_83 : match_parens_safety_wit_83.
Axiom proof_of_match_parens_safety_wit_84 : match_parens_safety_wit_84.
Axiom proof_of_match_parens_safety_wit_85 : match_parens_safety_wit_85.
Axiom proof_of_match_parens_safety_wit_86 : match_parens_safety_wit_86.
Axiom proof_of_match_parens_safety_wit_87 : match_parens_safety_wit_87.
Axiom proof_of_match_parens_safety_wit_88 : match_parens_safety_wit_88.
Axiom proof_of_match_parens_safety_wit_89 : match_parens_safety_wit_89.
Axiom proof_of_match_parens_safety_wit_90 : match_parens_safety_wit_90.
Axiom proof_of_match_parens_safety_wit_91 : match_parens_safety_wit_91.
Axiom proof_of_match_parens_safety_wit_92 : match_parens_safety_wit_92.
Axiom proof_of_match_parens_safety_wit_93 : match_parens_safety_wit_93.
Axiom proof_of_match_parens_safety_wit_94 : match_parens_safety_wit_94.
Axiom proof_of_match_parens_safety_wit_95 : match_parens_safety_wit_95.
Axiom proof_of_match_parens_safety_wit_96 : match_parens_safety_wit_96.
Axiom proof_of_match_parens_safety_wit_97 : match_parens_safety_wit_97.
Axiom proof_of_match_parens_safety_wit_98 : match_parens_safety_wit_98.
Axiom proof_of_match_parens_safety_wit_99 : match_parens_safety_wit_99.
Axiom proof_of_match_parens_safety_wit_100 : match_parens_safety_wit_100.
Axiom proof_of_match_parens_safety_wit_101 : match_parens_safety_wit_101.
Axiom proof_of_match_parens_safety_wit_102 : match_parens_safety_wit_102.
Axiom proof_of_match_parens_safety_wit_103 : match_parens_safety_wit_103.
Axiom proof_of_match_parens_safety_wit_104 : match_parens_safety_wit_104.
Axiom proof_of_match_parens_safety_wit_105 : match_parens_safety_wit_105.
Axiom proof_of_match_parens_safety_wit_106 : match_parens_safety_wit_106.
Axiom proof_of_match_parens_safety_wit_107 : match_parens_safety_wit_107.
Axiom proof_of_match_parens_safety_wit_108 : match_parens_safety_wit_108.
Axiom proof_of_match_parens_safety_wit_109 : match_parens_safety_wit_109.
Axiom proof_of_match_parens_safety_wit_110 : match_parens_safety_wit_110.
Axiom proof_of_match_parens_safety_wit_111 : match_parens_safety_wit_111.
Axiom proof_of_match_parens_safety_wit_112 : match_parens_safety_wit_112.
Axiom proof_of_match_parens_safety_wit_113 : match_parens_safety_wit_113.
Axiom proof_of_match_parens_entail_wit_1 : match_parens_entail_wit_1.
Axiom proof_of_match_parens_entail_wit_2_1 : match_parens_entail_wit_2_1.
Axiom proof_of_match_parens_entail_wit_2_2 : match_parens_entail_wit_2_2.
Axiom proof_of_match_parens_entail_wit_2_3 : match_parens_entail_wit_2_3.
Axiom proof_of_match_parens_entail_wit_2_4 : match_parens_entail_wit_2_4.
Axiom proof_of_match_parens_entail_wit_2_5 : match_parens_entail_wit_2_5.
Axiom proof_of_match_parens_entail_wit_2_6 : match_parens_entail_wit_2_6.
Axiom proof_of_match_parens_entail_wit_2_7 : match_parens_entail_wit_2_7.
Axiom proof_of_match_parens_entail_wit_2_8 : match_parens_entail_wit_2_8.
Axiom proof_of_match_parens_entail_wit_3_1 : match_parens_entail_wit_3_1.
Axiom proof_of_match_parens_entail_wit_3_2 : match_parens_entail_wit_3_2.
Axiom proof_of_match_parens_entail_wit_3_3 : match_parens_entail_wit_3_3.
Axiom proof_of_match_parens_entail_wit_3_4 : match_parens_entail_wit_3_4.
Axiom proof_of_match_parens_entail_wit_4_1 : match_parens_entail_wit_4_1.
Axiom proof_of_match_parens_entail_wit_4_2 : match_parens_entail_wit_4_2.
Axiom proof_of_match_parens_entail_wit_5_1 : match_parens_entail_wit_5_1.
Axiom proof_of_match_parens_entail_wit_5_2 : match_parens_entail_wit_5_2.
Axiom proof_of_match_parens_entail_wit_5_3 : match_parens_entail_wit_5_3.
Axiom proof_of_match_parens_entail_wit_5_4 : match_parens_entail_wit_5_4.
Axiom proof_of_match_parens_entail_wit_5_5 : match_parens_entail_wit_5_5.
Axiom proof_of_match_parens_entail_wit_5_6 : match_parens_entail_wit_5_6.
Axiom proof_of_match_parens_entail_wit_5_7 : match_parens_entail_wit_5_7.
Axiom proof_of_match_parens_entail_wit_5_8 : match_parens_entail_wit_5_8.
Axiom proof_of_match_parens_entail_wit_6_1 : match_parens_entail_wit_6_1.
Axiom proof_of_match_parens_entail_wit_6_2 : match_parens_entail_wit_6_2.
Axiom proof_of_match_parens_entail_wit_6_3 : match_parens_entail_wit_6_3.
Axiom proof_of_match_parens_entail_wit_6_4 : match_parens_entail_wit_6_4.
Axiom proof_of_match_parens_entail_wit_7_1 : match_parens_entail_wit_7_1.
Axiom proof_of_match_parens_entail_wit_7_2 : match_parens_entail_wit_7_2.
Axiom proof_of_match_parens_entail_wit_8 : match_parens_entail_wit_8.
Axiom proof_of_match_parens_entail_wit_9 : match_parens_entail_wit_9.
Axiom proof_of_match_parens_entail_wit_10_1 : match_parens_entail_wit_10_1.
Axiom proof_of_match_parens_entail_wit_10_2 : match_parens_entail_wit_10_2.
Axiom proof_of_match_parens_entail_wit_10_3 : match_parens_entail_wit_10_3.
Axiom proof_of_match_parens_entail_wit_10_4 : match_parens_entail_wit_10_4.
Axiom proof_of_match_parens_entail_wit_10_5 : match_parens_entail_wit_10_5.
Axiom proof_of_match_parens_entail_wit_10_6 : match_parens_entail_wit_10_6.
Axiom proof_of_match_parens_entail_wit_10_7 : match_parens_entail_wit_10_7.
Axiom proof_of_match_parens_entail_wit_10_8 : match_parens_entail_wit_10_8.
Axiom proof_of_match_parens_entail_wit_11_1 : match_parens_entail_wit_11_1.
Axiom proof_of_match_parens_entail_wit_11_2 : match_parens_entail_wit_11_2.
Axiom proof_of_match_parens_entail_wit_11_3 : match_parens_entail_wit_11_3.
Axiom proof_of_match_parens_entail_wit_11_4 : match_parens_entail_wit_11_4.
Axiom proof_of_match_parens_entail_wit_12_1 : match_parens_entail_wit_12_1.
Axiom proof_of_match_parens_entail_wit_12_2 : match_parens_entail_wit_12_2.
Axiom proof_of_match_parens_entail_wit_13_1 : match_parens_entail_wit_13_1.
Axiom proof_of_match_parens_entail_wit_13_2 : match_parens_entail_wit_13_2.
Axiom proof_of_match_parens_entail_wit_13_3 : match_parens_entail_wit_13_3.
Axiom proof_of_match_parens_entail_wit_13_4 : match_parens_entail_wit_13_4.
Axiom proof_of_match_parens_entail_wit_13_5 : match_parens_entail_wit_13_5.
Axiom proof_of_match_parens_entail_wit_13_6 : match_parens_entail_wit_13_6.
Axiom proof_of_match_parens_entail_wit_13_7 : match_parens_entail_wit_13_7.
Axiom proof_of_match_parens_entail_wit_13_8 : match_parens_entail_wit_13_8.
Axiom proof_of_match_parens_entail_wit_14_1 : match_parens_entail_wit_14_1.
Axiom proof_of_match_parens_entail_wit_14_2 : match_parens_entail_wit_14_2.
Axiom proof_of_match_parens_entail_wit_14_3 : match_parens_entail_wit_14_3.
Axiom proof_of_match_parens_entail_wit_14_4 : match_parens_entail_wit_14_4.
Axiom proof_of_match_parens_entail_wit_15 : match_parens_entail_wit_15.
Axiom proof_of_match_parens_entail_wit_16 : match_parens_entail_wit_16.
Axiom proof_of_match_parens_return_wit_1 : match_parens_return_wit_1.
Axiom proof_of_match_parens_return_wit_2 : match_parens_return_wit_2.
Axiom proof_of_match_parens_return_wit_3 : match_parens_return_wit_3.
Axiom proof_of_match_parens_return_wit_4 : match_parens_return_wit_4.
Axiom proof_of_match_parens_partial_solve_wit_1_pure : match_parens_partial_solve_wit_1_pure.
Axiom proof_of_match_parens_partial_solve_wit_1 : match_parens_partial_solve_wit_1.
Axiom proof_of_match_parens_partial_solve_wit_2_pure : match_parens_partial_solve_wit_2_pure.
Axiom proof_of_match_parens_partial_solve_wit_2 : match_parens_partial_solve_wit_2.

End VC_Correct.
