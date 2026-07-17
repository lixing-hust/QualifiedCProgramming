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
Require Import coins_66.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function digitSum -----*)

Definition digitSum_safety_wit_1 := 
forall (s_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_66_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) (PreH4 : (upper_sum_safe_66 input )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digitSum_safety_wit_2 := 
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_66_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (upper_sum_safe_66 input )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digitSum_safety_wit_3 := 
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_66_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (upper_sum_safe_66 input )) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition digitSum_safety_wit_4 := 
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) >= 65)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_66_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (upper_sum_safe_66 input )) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition digitSum_safety_wit_5 := 
(
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ ((sum + (Znth i (c_string (input)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i (c_string (input)) 0) )) ”
) \/
(
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ ((sum + (Znth i (c_string (input)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i (c_string (input)) 0) )) ”
).

Definition digitSum_safety_wit_5_split_goal_1 := 
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ ((sum + (Znth i (c_string (input)) 0) ) <= INT_MAX) ”
.

Definition digitSum_safety_wit_5_split_goal_2 := 
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ ((INT_MIN) <= (sum + (Znth i (c_string (input)) 0) )) ”
.

Definition digitSum_safety_wit_6 := 
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i (c_string (input)) 0) ))
  **  (store_string s_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition digitSum_safety_wit_7 := 
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 65)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_66_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (upper_sum_safe_66 input )) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition digitSum_safety_wit_8 := 
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) > 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (store_string s_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition digitSum_entail_wit_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_66_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (upper_sum_safe_66 input )) ,
  (store_string s_pre input )
|--
  “ (retval = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_66_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (upper_sum_safe_66 input ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 = (upper_sum_prefix_66 (0) (input))) ”
  &&  (store_string s_pre input )
) \/
(
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_66_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (upper_sum_safe_66 input )) ,
  TT && emp 
|--
  “ (0 = (upper_sum_prefix_66 (0) (input))) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition digitSum_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_66_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (upper_sum_safe_66 input )) ,
  TT && emp 
|--
  “ (0 = (upper_sum_prefix_66 (0) (input))) ”
.

Definition digitSum_entail_wit_1_split_goal_2 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_66_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (upper_sum_safe_66 input )) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition digitSum_entail_wit_2_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <= 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  (store_string s_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_66_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (upper_sum_safe_66 input ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ ((sum + (Znth i (c_string (input)) 0) ) = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
  &&  (store_string s_pre input )
) \/
(
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_66_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (upper_sum_safe_66 input )) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ ((sum + (Znth i (c_string (input)) 0) ) = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
  &&  emp
).

Definition digitSum_entail_wit_2_1_split_goal_1 := 
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <= 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_66_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (upper_sum_safe_66 input )) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ ((sum + (Znth i (c_string (input)) 0) ) = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
.

Definition digitSum_entail_wit_2_2 := 
(
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 65)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_66_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (upper_sum_safe_66 input )) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  (store_string s_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_66_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (upper_sum_safe_66 input ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
  &&  (store_string s_pre input )
) \/
(
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ (sum = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
  &&  emp
).

Definition digitSum_entail_wit_2_2_split_goal_1 := 
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ (sum = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
.

Definition digitSum_entail_wit_2_3 := 
(
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) > 90)) (PreH2 : ((Znth i (c_string (input)) 0) >= 65)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_66_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (upper_sum_safe_66 input )) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  (store_string s_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_66_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (upper_sum_safe_66 input ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
  &&  (store_string s_pre input )
) \/
(
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) > 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_66_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (upper_sum_safe_66 input )) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ (sum = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
  &&  emp
).

Definition digitSum_entail_wit_2_3_split_goal_1 := 
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) > 90)) (PreH3 : ((Znth i (c_string (input)) 0) >= 65)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_66_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (upper_sum_safe_66 input )) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ (sum = (upper_sum_prefix_66 ((i + 1 )) (input))) ”
.

Definition digitSum_return_wit_1 := 
(
forall (s_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_66_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (upper_sum_safe_66 input )) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  (store_string s_pre input )
|--
  “ (problem_66_spec_z input sum ) ”
  &&  (store_string s_pre input )
) \/
(
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_66_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (upper_sum_safe_66 input )) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ (problem_66_spec_z input sum ) ”
  &&  emp
).

Definition digitSum_return_wit_1_split_goal_1 := 
forall (input: (@list Z)) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_66_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (upper_sum_safe_66 input )) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (upper_sum_prefix_66 (i) (input)))) ,
  TT && emp 
|--
  “ (problem_66_spec_z input sum ) ”
.

Definition digitSum_partial_solve_wit_1_pure := 
forall (s_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_66_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) (PreH4 : (upper_sum_safe_66 input )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition digitSum_partial_solve_wit_1_aux := 
forall (s_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_66_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) (PreH4 : (upper_sum_safe_66 input )) ,
  (store_string s_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_66_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (upper_sum_safe_66 input ) ”
  &&  (store_string s_pre input )
.

Definition digitSum_partial_solve_wit_1 := digitSum_partial_solve_wit_1_pure -> digitSum_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_digitSum_safety_wit_1 : digitSum_safety_wit_1.
Axiom proof_of_digitSum_safety_wit_2 : digitSum_safety_wit_2.
Axiom proof_of_digitSum_safety_wit_3 : digitSum_safety_wit_3.
Axiom proof_of_digitSum_safety_wit_4 : digitSum_safety_wit_4.
Axiom proof_of_digitSum_safety_wit_5 : digitSum_safety_wit_5.
Axiom proof_of_digitSum_safety_wit_6 : digitSum_safety_wit_6.
Axiom proof_of_digitSum_safety_wit_7 : digitSum_safety_wit_7.
Axiom proof_of_digitSum_safety_wit_8 : digitSum_safety_wit_8.
Axiom proof_of_digitSum_entail_wit_1 : digitSum_entail_wit_1.
Axiom proof_of_digitSum_entail_wit_2_1 : digitSum_entail_wit_2_1.
Axiom proof_of_digitSum_entail_wit_2_2 : digitSum_entail_wit_2_2.
Axiom proof_of_digitSum_entail_wit_2_3 : digitSum_entail_wit_2_3.
Axiom proof_of_digitSum_return_wit_1 : digitSum_return_wit_1.
Axiom proof_of_digitSum_partial_solve_wit_1_pure : digitSum_partial_solve_wit_1_pure.
Axiom proof_of_digitSum_partial_solve_wit_1 : digitSum_partial_solve_wit_1.

End VC_Correct.
