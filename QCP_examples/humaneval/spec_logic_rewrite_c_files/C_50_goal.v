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
Require Import coins_50.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function encode_shift -----*)

Definition encode_shift_safety_wit_1 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition encode_shift_safety_wit_2 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition encode_shift_safety_wit_3 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (l)))) (PreH3 : (0 <= ((string_length (l)) + 1 ))) (PreH4 : (s_pre = s0)) (PreH5 : (problem_50_pre_z l )) (PreH6 : (valid_string l )) (PreH7 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition encode_shift_safety_wit_4 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ False ”
.

Definition encode_shift_safety_wit_5 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition encode_shift_safety_wit_6 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) ”
) \/
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) ”
).

Definition encode_shift_safety_wit_6_split_goal_1 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ”
.

Definition encode_shift_safety_wit_6_split_goal_2 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= (((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) ”
.

Definition encode_shift_safety_wit_7 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((((Znth i (c_string (l)) 0) + 5 ) - 97 ) <> (INT_MIN)) \/ (26 <> (-1))) ” 
  &&  “ (26 <> 0) ”
.

Definition encode_shift_safety_wit_8 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (l)) 0) + 5 ) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i (c_string (l)) 0) + 5 ) - 97 )) ”
) \/
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (l)) 0) + 5 ) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i (c_string (l)) 0) + 5 ) - 97 )) ”
).

Definition encode_shift_safety_wit_8_split_goal_1 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (l)) 0) + 5 ) - 97 ) <= INT_MAX) ”
.

Definition encode_shift_safety_wit_8_split_goal_2 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= (((Znth i (c_string (l)) 0) + 5 ) - 97 )) ”
.

Definition encode_shift_safety_wit_9 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (l)) 0) + 5 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (l)) 0) + 5 )) ”
) \/
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (l)) 0) + 5 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (l)) 0) + 5 )) ”
).

Definition encode_shift_safety_wit_9_split_goal_1 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (l)) 0) + 5 ) <= INT_MAX) ”
.

Definition encode_shift_safety_wit_9_split_goal_2 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (l)) 0) + 5 )) ”
.

Definition encode_shift_safety_wit_10 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition encode_shift_safety_wit_11 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition encode_shift_safety_wit_12 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (26 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 26) ”
.

Definition encode_shift_safety_wit_13 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition encode_shift_safety_wit_14 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l)) = i)) (PreH9 : (encode_prefix_50 l out_l )) ,
  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition encode_shift_safety_wit_15 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition encode_shift_entail_wit_1 := 
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  EX (out_l: (@list Z)) ,
  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (retval = (string_length (l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ (encode_prefix_50 l out_l ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s0)
  **  (store_string s0 l )
  **  (CharArray.full retval_2 0 out_l )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
) \/
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ (encode_prefix_50 l (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
).

Definition encode_shift_entail_wit_1_split_goal_1 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ (encode_prefix_50 l (@nil Z) ) ”
.

Definition encode_shift_entail_wit_1_split_goal_2 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition encode_shift_entail_wit_1_split_goal_3 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ (0 <= retval) ”
.

Definition encode_shift_entail_wit_1_split_goal_spatial := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
.

Definition encode_shift_entail_wit_2 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (encode_prefix_50 l out_l_2 )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (n = (string_length (l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ (encode_prefix_50 l out_l ) ”
  &&  (store_string s0 l )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (encode_prefix_50 l out_l_2 )) ,
  TT && emp 
|--
  “ (encode_prefix_50 l (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition encode_shift_entail_wit_2_split_goal_1 := 
forall (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (encode_prefix_50 l out_l_2 )) ,
  TT && emp 
|--
  “ (encode_prefix_50 l (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) ) ”
.

Definition encode_shift_entail_wit_2_split_goal_2 := 
forall (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (encode_prefix_50 l out_l_2 )) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))))) = (i + 1 )) ”
.

Definition encode_shift_return_wit_1 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (encode_prefix_50 l out_l_2 )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (n + 1 ) (n + 1 ) )
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
|--
  EX (out_l: (@list Z)) ,
  “ (encode_prefix_50 l out_l ) ” 
  &&  “ ((Zlength (out_l)) = (string_length (l))) ”
  &&  (store_string s0 l )
  **  (store_string out out_l )
) \/
(
forall (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (n = (string_length (l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : ((Zlength (out_l_2)) = i)) (PreH10 : (encode_prefix_50 l out_l_2 )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (encode_prefix_50 l out_l ) ” 
  &&  “ ((Zlength (out_l)) = (string_length (l))) ”
  &&  (CharArray.full out ((string_length (out_l)) + 1 ) (c_string (out_l)) )
).

Definition encode_shift_partial_solve_wit_1_pure := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (PreH1 : (s_pre = s0)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre l )
|--
  “ (valid_string l ) ” 
  &&  “ ((string_length (l)) < INT_MAX) ”
.

Definition encode_shift_partial_solve_wit_1_aux := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (PreH1 : (s_pre = s0)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre l )
|--
  “ (valid_string l ) ” 
  &&  “ ((string_length (l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (((string_length (l)) + 1 ) < INT_MAX) ”
  &&  (store_string s_pre l )
.

Definition encode_shift_partial_solve_wit_1 := encode_shift_partial_solve_wit_1_pure -> encode_shift_partial_solve_wit_1_aux.

Definition encode_shift_partial_solve_wit_2_pure := 
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ”
) \/
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 < (retval + 1 )) ”
).

Definition encode_shift_partial_solve_wit_2_pure_split_goal_1 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 < (retval + 1 )) ”
.

Definition encode_shift_partial_solve_wit_2_aux := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre l )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ” 
  &&  “ (retval = (string_length (l))) ” 
  &&  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (((string_length (l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
.

Definition encode_shift_partial_solve_wit_2 := encode_shift_partial_solve_wit_2_pure -> encode_shift_partial_solve_wit_2_aux.

Definition encode_shift_partial_solve_wit_3 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  (store_string s0 l )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (n = (string_length (l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (encode_prefix_50 l out_l ) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i out_l )
.

Definition encode_shift_partial_solve_wit_4 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (encode_prefix_50 l out_l )) ,
  (store_string s0 l )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (i >= n) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (n = (string_length (l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (encode_prefix_50 l out_l ) ”
  &&  (((out + (n * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_missing_i out n i (n + 1 ) )
  **  (CharArray.full out i out_l )
.

(*----- Function decode_shift -----*)

Definition decode_shift_safety_wit_1 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition decode_shift_safety_wit_2 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decode_shift_safety_wit_3 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (l)))) (PreH3 : (0 <= ((string_length (l)) + 1 ))) (PreH4 : (s_pre = s0)) (PreH5 : (problem_50_pre_z l )) (PreH6 : (valid_string l )) (PreH7 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decode_shift_safety_wit_4 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ False ”
.

Definition decode_shift_safety_wit_5 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decode_shift_safety_wit_6 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) ”
) \/
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) ”
).

Definition decode_shift_safety_wit_6_split_goal_1 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) ”
.

Definition decode_shift_safety_wit_6_split_goal_2 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= (((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) ”
.

Definition decode_shift_safety_wit_7 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((((Znth i (c_string (l)) 0) + 21 ) - 97 ) <> (INT_MIN)) \/ (26 <> (-1))) ” 
  &&  “ (26 <> 0) ”
.

Definition decode_shift_safety_wit_8 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (l)) 0) + 21 ) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i (c_string (l)) 0) + 21 ) - 97 )) ”
) \/
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (l)) 0) + 21 ) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i (c_string (l)) 0) + 21 ) - 97 )) ”
).

Definition decode_shift_safety_wit_8_split_goal_1 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((Znth i (c_string (l)) 0) + 21 ) - 97 ) <= INT_MAX) ”
.

Definition decode_shift_safety_wit_8_split_goal_2 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= (((Znth i (c_string (l)) 0) + 21 ) - 97 )) ”
.

Definition decode_shift_safety_wit_9 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (l)) 0) + 21 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (l)) 0) + 21 )) ”
) \/
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (l)) 0) + 21 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (l)) 0) + 21 )) ”
).

Definition decode_shift_safety_wit_9_split_goal_1 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((Znth i (c_string (l)) 0) + 21 ) <= INT_MAX) ”
.

Definition decode_shift_safety_wit_9_split_goal_2 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (l)) 0) + 21 )) ”
.

Definition decode_shift_safety_wit_10 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (21 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 21) ”
.

Definition decode_shift_safety_wit_11 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition decode_shift_safety_wit_12 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (26 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 26) ”
.

Definition decode_shift_safety_wit_13 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition decode_shift_safety_wit_14 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l)) = i)) (PreH9 : (decode_prefix_50 l out_l )) ,
  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition decode_shift_safety_wit_15 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  ((( &( "s" ) )) # Ptr  |-> s0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s0 l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decode_shift_entail_wit_1 := 
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  EX (out_l: (@list Z)) ,
  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (retval = (string_length (l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ (decode_prefix_50 l out_l ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s0)
  **  (store_string s0 l )
  **  (CharArray.full retval_2 0 out_l )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
) \/
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ (decode_prefix_50 l (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
).

Definition decode_shift_entail_wit_1_split_goal_1 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ (decode_prefix_50 l (@nil Z) ) ”
.

Definition decode_shift_entail_wit_1_split_goal_2 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition decode_shift_entail_wit_1_split_goal_3 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  “ (0 <= retval) ”
.

Definition decode_shift_entail_wit_1_split_goal_spatial := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
|--
  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
.

Definition decode_shift_entail_wit_2 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (decode_prefix_50 l out_l_2 )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (n = (string_length (l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ (decode_prefix_50 l out_l ) ”
  &&  (store_string s0 l )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (decode_prefix_50 l out_l_2 )) ,
  TT && emp 
|--
  “ (decode_prefix_50 l (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition decode_shift_entail_wit_2_split_goal_1 := 
forall (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (decode_prefix_50 l out_l_2 )) ,
  TT && emp 
|--
  “ (decode_prefix_50 l (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))) ) ”
.

Definition decode_shift_entail_wit_2_split_goal_2 := 
forall (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i < n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (decode_prefix_50 l out_l_2 )) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (c_string (l)) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) ((@nil Z))))))) = (i + 1 )) ”
.

Definition decode_shift_return_wit_1 := 
(
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (problem_50_pre_z l )) (PreH4 : (valid_string l )) (PreH5 : (n = (string_length (l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : ((Zlength (out_l_2)) = i)) (PreH9 : (decode_prefix_50 l out_l_2 )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (n + 1 ) (n + 1 ) )
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_50_spec_z l out_l ) ” 
  &&  “ ((Zlength (out_l)) = (string_length (l))) ”
  &&  (store_string s0 l )
  **  (store_string out out_l )
) \/
(
forall (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (n = (string_length (l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : ((Zlength (out_l_2)) = i)) (PreH10 : (decode_prefix_50 l out_l_2 )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_50_spec_z l out_l ) ” 
  &&  “ ((Zlength (out_l)) = (string_length (l))) ”
  &&  (CharArray.full out ((string_length (out_l)) + 1 ) (c_string (out_l)) )
).

Definition decode_shift_partial_solve_wit_1_pure := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (PreH1 : (s_pre = s0)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre l )
|--
  “ (valid_string l ) ” 
  &&  “ ((string_length (l)) < INT_MAX) ”
.

Definition decode_shift_partial_solve_wit_1_aux := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (PreH1 : (s_pre = s0)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre l )
|--
  “ (valid_string l ) ” 
  &&  “ ((string_length (l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (((string_length (l)) + 1 ) < INT_MAX) ”
  &&  (store_string s_pre l )
.

Definition decode_shift_partial_solve_wit_1 := decode_shift_partial_solve_wit_1_pure -> decode_shift_partial_solve_wit_1_aux.

Definition decode_shift_partial_solve_wit_2_pure := 
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ”
) \/
(
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 < (retval + 1 )) ”
).

Definition decode_shift_partial_solve_wit_2_pure_split_goal_1 := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (l)))) (PreH4 : (0 <= ((string_length (l)) + 1 ))) (PreH5 : (s_pre = s0)) (PreH6 : (problem_50_pre_z l )) (PreH7 : (valid_string l )) (PreH8 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 < (retval + 1 )) ”
.

Definition decode_shift_partial_solve_wit_2_aux := 
forall (s_pre: Z) (s0: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (l)))) (PreH2 : (0 <= ((string_length (l)) + 1 ))) (PreH3 : (s_pre = s0)) (PreH4 : (problem_50_pre_z l )) (PreH5 : (valid_string l )) (PreH6 : (((string_length (l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre l )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (0 < (retval + 1 )) ” 
  &&  “ (retval = (string_length (l))) ” 
  &&  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (s_pre = s0) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (((string_length (l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (l)) + 1 ) (c_string (l)) )
.

Definition decode_shift_partial_solve_wit_2 := decode_shift_partial_solve_wit_2_pure -> decode_shift_partial_solve_wit_2_aux.

Definition decode_shift_partial_solve_wit_3 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  (store_string s0 l )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (n = (string_length (l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (decode_prefix_50 l out_l ) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full out i out_l )
.

Definition decode_shift_partial_solve_wit_4 := 
forall (s0: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (problem_50_pre_z l )) (PreH3 : (valid_string l )) (PreH4 : (n = (string_length (l)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : ((Zlength (out_l)) = i)) (PreH8 : (decode_prefix_50 l out_l )) ,
  (store_string s0 l )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= ((string_length (l)) + 1 )) ” 
  &&  “ (i >= n) ” 
  &&  “ (problem_50_pre_z l ) ” 
  &&  “ (valid_string l ) ” 
  &&  “ (n = (string_length (l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (decode_prefix_50 l out_l ) ”
  &&  (((out + (n * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s0 ((string_length (l)) + 1 ) (c_string (l)) )
  **  (CharArray.undef_missing_i out n i (n + 1 ) )
  **  (CharArray.full out i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_encode_shift_safety_wit_1 : encode_shift_safety_wit_1.
Axiom proof_of_encode_shift_safety_wit_2 : encode_shift_safety_wit_2.
Axiom proof_of_encode_shift_safety_wit_3 : encode_shift_safety_wit_3.
Axiom proof_of_encode_shift_safety_wit_4 : encode_shift_safety_wit_4.
Axiom proof_of_encode_shift_safety_wit_5 : encode_shift_safety_wit_5.
Axiom proof_of_encode_shift_safety_wit_6 : encode_shift_safety_wit_6.
Axiom proof_of_encode_shift_safety_wit_7 : encode_shift_safety_wit_7.
Axiom proof_of_encode_shift_safety_wit_8 : encode_shift_safety_wit_8.
Axiom proof_of_encode_shift_safety_wit_9 : encode_shift_safety_wit_9.
Axiom proof_of_encode_shift_safety_wit_10 : encode_shift_safety_wit_10.
Axiom proof_of_encode_shift_safety_wit_11 : encode_shift_safety_wit_11.
Axiom proof_of_encode_shift_safety_wit_12 : encode_shift_safety_wit_12.
Axiom proof_of_encode_shift_safety_wit_13 : encode_shift_safety_wit_13.
Axiom proof_of_encode_shift_safety_wit_14 : encode_shift_safety_wit_14.
Axiom proof_of_encode_shift_safety_wit_15 : encode_shift_safety_wit_15.
Axiom proof_of_encode_shift_entail_wit_1 : encode_shift_entail_wit_1.
Axiom proof_of_encode_shift_entail_wit_2 : encode_shift_entail_wit_2.
Axiom proof_of_encode_shift_return_wit_1 : encode_shift_return_wit_1.
Axiom proof_of_encode_shift_partial_solve_wit_1_pure : encode_shift_partial_solve_wit_1_pure.
Axiom proof_of_encode_shift_partial_solve_wit_1 : encode_shift_partial_solve_wit_1.
Axiom proof_of_encode_shift_partial_solve_wit_2_pure : encode_shift_partial_solve_wit_2_pure.
Axiom proof_of_encode_shift_partial_solve_wit_2 : encode_shift_partial_solve_wit_2.
Axiom proof_of_encode_shift_partial_solve_wit_3 : encode_shift_partial_solve_wit_3.
Axiom proof_of_encode_shift_partial_solve_wit_4 : encode_shift_partial_solve_wit_4.
Axiom proof_of_decode_shift_safety_wit_1 : decode_shift_safety_wit_1.
Axiom proof_of_decode_shift_safety_wit_2 : decode_shift_safety_wit_2.
Axiom proof_of_decode_shift_safety_wit_3 : decode_shift_safety_wit_3.
Axiom proof_of_decode_shift_safety_wit_4 : decode_shift_safety_wit_4.
Axiom proof_of_decode_shift_safety_wit_5 : decode_shift_safety_wit_5.
Axiom proof_of_decode_shift_safety_wit_6 : decode_shift_safety_wit_6.
Axiom proof_of_decode_shift_safety_wit_7 : decode_shift_safety_wit_7.
Axiom proof_of_decode_shift_safety_wit_8 : decode_shift_safety_wit_8.
Axiom proof_of_decode_shift_safety_wit_9 : decode_shift_safety_wit_9.
Axiom proof_of_decode_shift_safety_wit_10 : decode_shift_safety_wit_10.
Axiom proof_of_decode_shift_safety_wit_11 : decode_shift_safety_wit_11.
Axiom proof_of_decode_shift_safety_wit_12 : decode_shift_safety_wit_12.
Axiom proof_of_decode_shift_safety_wit_13 : decode_shift_safety_wit_13.
Axiom proof_of_decode_shift_safety_wit_14 : decode_shift_safety_wit_14.
Axiom proof_of_decode_shift_safety_wit_15 : decode_shift_safety_wit_15.
Axiom proof_of_decode_shift_entail_wit_1 : decode_shift_entail_wit_1.
Axiom proof_of_decode_shift_entail_wit_2 : decode_shift_entail_wit_2.
Axiom proof_of_decode_shift_return_wit_1 : decode_shift_return_wit_1.
Axiom proof_of_decode_shift_partial_solve_wit_1_pure : decode_shift_partial_solve_wit_1_pure.
Axiom proof_of_decode_shift_partial_solve_wit_1 : decode_shift_partial_solve_wit_1.
Axiom proof_of_decode_shift_partial_solve_wit_2_pure : decode_shift_partial_solve_wit_2_pure.
Axiom proof_of_decode_shift_partial_solve_wit_2 : decode_shift_partial_solve_wit_2.
Axiom proof_of_decode_shift_partial_solve_wit_3 : decode_shift_partial_solve_wit_3.
Axiom proof_of_decode_shift_partial_solve_wit_4 : decode_shift_partial_solve_wit_4.

End VC_Correct.
