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
Require Import coins_86.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function anti_shuffle -----*)

Definition anti_shuffle_safety_wit_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_86_pre_z str_l )) (PreH6 : (anti_shuffle_safe_86 str_l )) (PreH7 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition anti_shuffle_safety_wit_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_86_pre_z str_l )) (PreH6 : (anti_shuffle_safe_86 str_l )) (PreH7 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_86_pre_z str_l )) (PreH7 : (anti_shuffle_safe_86 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition anti_shuffle_safety_wit_4 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_86_pre_z str_l )) (PreH7 : (anti_shuffle_safe_86 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_5 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out_len" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_6 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cur_len" ) )) # Int  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_7 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "first" ) )) # Int  |->_)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_8 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> 1)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_9 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "first" ) )) # Int  |-> 1)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_10 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition anti_shuffle_safety_wit_11 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition anti_shuffle_safety_wit_12 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur (cur_len + 1 ) (app (cur_l) ((cons ((signed_last_nbits ((Znth i (c_string (str_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((cur_len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur_len + 1 )) ”
.

Definition anti_shuffle_safety_wit_13 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur (cur_len + 1 ) (app (cur_l) ((cons ((signed_last_nbits ((Znth i (c_string (str_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_14 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur (cur_len + 1 ) (app (cur_l) ((cons ((signed_last_nbits ((Znth i (c_string (str_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ ((cur_len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur_len + 1 )) ”
.

Definition anti_shuffle_safety_wit_15 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur (cur_len + 1 ) (app (cur_l) ((cons ((signed_last_nbits ((Znth i (c_string (str_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_16 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_17 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_18 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_19 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_20 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (1 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l)) = out_len)) (PreH11 : ((Zlength (cur_l)) = cur_len)) (PreH12 : ((Zlength (sorted_l)) = cur_len)) (PreH13 : (all_ascii sorted_l )) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (anti_shuffle_commit_index_86 str_l i )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_21 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (1 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l)) = out_len)) (PreH11 : ((Zlength (cur_l)) = cur_len)) (PreH12 : ((Zlength (sorted_l)) = cur_len)) (PreH13 : (all_ascii sorted_l )) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (anti_shuffle_commit_index_86 str_l i )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_22 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 <= cur_len)) (PreH9 : (cur_len <= 1)) (PreH10 : ((Zlength (out_l)) = out_len)) (PreH11 : ((Zlength (cur_l)) = cur_len)) (PreH12 : (sorted_l = cur_l)) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_23 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 <= cur_len)) (PreH9 : (cur_len <= 1)) (PreH10 : ((Zlength (out_l)) = out_len)) (PreH11 : ((Zlength (cur_l)) = cur_len)) (PreH12 : (sorted_l = cur_l)) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_24 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (1 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ False ”
.

Definition anti_shuffle_safety_wit_25 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (1 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ False ”
.

Definition anti_shuffle_safety_wit_26 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= 1)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : (sorted_l = cur_l)) (PreH14 : ((Zlength (sorted_l)) = cur_len)) (PreH15 : (all_ascii sorted_l )) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (anti_shuffle_commit_index_86 str_l i )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ False ”
.

Definition anti_shuffle_safety_wit_27 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= 1)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : (sorted_l = cur_l)) (PreH14 : ((Zlength (sorted_l)) = cur_len)) (PreH15 : (all_ascii sorted_l )) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (anti_shuffle_commit_index_86 str_l i )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ False ”
.

Definition anti_shuffle_safety_wit_28 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (1 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition anti_shuffle_safety_wit_29 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= 1)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : (sorted_l = cur_l)) (PreH14 : ((Zlength (sorted_l)) = cur_len)) (PreH15 : (all_ascii sorted_l )) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (anti_shuffle_commit_index_86 str_l i )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition anti_shuffle_safety_wit_30 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (first = 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (1 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : ((Zlength (sorted_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((out_len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + 1 )) ”
.

Definition anti_shuffle_safety_wit_31 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (first = 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (1 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : ((Zlength (sorted_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_32 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (first = 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= 1)) (PreH12 : ((Zlength (out_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (sorted_l = cur_l)) (PreH15 : ((Zlength (sorted_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((out_len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + 1 )) ”
.

Definition anti_shuffle_safety_wit_33 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (first = 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= 1)) (PreH12 : ((Zlength (out_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (sorted_l = cur_l)) (PreH15 : ((Zlength (sorted_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_34 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (1 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 <= cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l)) = (out_len - 1 ))) (PreH11 : (out_sep_l = (app (out_l) ((cons (32) ((@nil Z))))))) (PreH12 : ((Zlength (out_sep_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : ((Zlength (sorted_l)) = cur_len)) (PreH15 : (all_ascii sorted_l )) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (anti_shuffle_commit_index_86 str_l i )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_35 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 <= cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l)) = out_len)) (PreH11 : (out_sep_l = out_l)) (PreH12 : ((Zlength (out_sep_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : ((Zlength (sorted_l)) = cur_len)) (PreH15 : (all_ascii sorted_l )) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (anti_shuffle_commit_index_86 str_l i )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_36 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (cur_len > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (1 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l)) = (out_len - 1 ))) (PreH12 : (out_sep_l = (app (out_l) ((cons (32) ((@nil Z))))))) (PreH13 : ((Zlength (out_sep_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : ((Zlength (sorted_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "copy" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_37 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (cur_len > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : (out_sep_l = out_l)) (PreH13 : ((Zlength (out_sep_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : ((Zlength (sorted_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "copy" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_38 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (out_len + copy ))) (PreH3 : (copy < cur_len)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : (0 <= copy)) (PreH14 : (copy <= cur_len)) (PreH15 : ((out_len + cur_len ) <= n)) (PreH16 : ((out_len + copy ) <= n)) (PreH17 : ((Zlength (out_sep_l)) = out_len)) (PreH18 : ((Zlength (sorted_l)) = cur_len)) (PreH19 : ((Zlength (cur_l)) = cur_len)) (PreH20 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH21 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH22 : (out_sep_relation_86 first out_l out_sep_l )) (PreH23 : (all_ascii sorted_l )) (PreH24 : (first = 1)) (PreH25 : (0 <= ch)) (PreH26 : (ch <= 127)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (problem_86_pre_z str_l )) (PreH30 : (anti_shuffle_safe_86 str_l )) (PreH31 : (anti_shuffle_commit_index_86 str_l i )) (PreH32 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH33 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH34 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth copy sorted_l 0))
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((out_len + copy ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + copy )) ”
.

Definition anti_shuffle_safety_wit_39 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (out_len + copy ))) (PreH3 : (copy < cur_len)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : (0 <= copy)) (PreH14 : (copy <= cur_len)) (PreH15 : ((out_len + cur_len ) <= n)) (PreH16 : ((out_len + copy ) <= n)) (PreH17 : ((Zlength (out_sep_l)) = out_len)) (PreH18 : ((Zlength (sorted_l)) = cur_len)) (PreH19 : ((Zlength (cur_l)) = cur_len)) (PreH20 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH21 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH22 : (out_sep_relation_86 first out_l out_sep_l )) (PreH23 : (all_ascii sorted_l )) (PreH24 : (first = 0)) (PreH25 : (0 <= ch)) (PreH26 : (ch <= 127)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (problem_86_pre_z str_l )) (PreH30 : (anti_shuffle_safe_86 str_l )) (PreH31 : (anti_shuffle_commit_index_86 str_l i )) (PreH32 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH33 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH34 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth copy sorted_l 0))
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((out_len + copy ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + copy )) ”
.

Definition anti_shuffle_safety_wit_40 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= cur_len)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= (out_len + copy ))) (PreH4 : (copy < cur_len)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 < cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : (0 <= copy)) (PreH15 : (copy <= cur_len)) (PreH16 : ((out_len + cur_len ) <= n)) (PreH17 : ((out_len + copy ) <= n)) (PreH18 : ((Zlength (out_sep_l)) = out_len)) (PreH19 : ((Zlength (sorted_l)) = cur_len)) (PreH20 : ((Zlength (cur_l)) = cur_len)) (PreH21 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH22 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH23 : (out_sep_relation_86 first out_l out_sep_l )) (PreH24 : (all_ascii sorted_l )) (PreH25 : (first = 0)) (PreH26 : (0 <= ch)) (PreH27 : (ch <= 127)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (problem_86_pre_z str_l )) (PreH31 : (anti_shuffle_safe_86 str_l )) (PreH32 : (anti_shuffle_commit_index_86 str_l i )) (PreH33 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH34 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH35 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out ((out_len + copy ) + 1 ) (app (out_copy_l) ((cons ((signed_last_nbits ((Znth copy sorted_l 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((out_len + copy ) + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth copy sorted_l 0))
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((copy + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (copy + 1 )) ”
.

Definition anti_shuffle_safety_wit_41 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= cur_len)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= (out_len + copy ))) (PreH4 : (copy < cur_len)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 < cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : (0 <= copy)) (PreH15 : (copy <= cur_len)) (PreH16 : ((out_len + cur_len ) <= n)) (PreH17 : ((out_len + copy ) <= n)) (PreH18 : ((Zlength (out_sep_l)) = out_len)) (PreH19 : ((Zlength (sorted_l)) = cur_len)) (PreH20 : ((Zlength (cur_l)) = cur_len)) (PreH21 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH22 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH23 : (out_sep_relation_86 first out_l out_sep_l )) (PreH24 : (all_ascii sorted_l )) (PreH25 : (first = 0)) (PreH26 : (0 <= ch)) (PreH27 : (ch <= 127)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (problem_86_pre_z str_l )) (PreH31 : (anti_shuffle_safe_86 str_l )) (PreH32 : (anti_shuffle_commit_index_86 str_l i )) (PreH33 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH34 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH35 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out ((out_len + copy ) + 1 ) (app (out_copy_l) ((cons ((signed_last_nbits ((Znth copy sorted_l 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((out_len + copy ) + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth copy sorted_l 0))
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_42 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= cur_len)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= (out_len + copy ))) (PreH4 : (copy < cur_len)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 < cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : (0 <= copy)) (PreH15 : (copy <= cur_len)) (PreH16 : ((out_len + cur_len ) <= n)) (PreH17 : ((out_len + copy ) <= n)) (PreH18 : ((Zlength (out_sep_l)) = out_len)) (PreH19 : ((Zlength (sorted_l)) = cur_len)) (PreH20 : ((Zlength (cur_l)) = cur_len)) (PreH21 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH22 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH23 : (out_sep_relation_86 first out_l out_sep_l )) (PreH24 : (all_ascii sorted_l )) (PreH25 : (first = 1)) (PreH26 : (0 <= ch)) (PreH27 : (ch <= 127)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (problem_86_pre_z str_l )) (PreH31 : (anti_shuffle_safe_86 str_l )) (PreH32 : (anti_shuffle_commit_index_86 str_l i )) (PreH33 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH34 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH35 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out ((out_len + copy ) + 1 ) (app (out_copy_l) ((cons ((signed_last_nbits ((Znth copy sorted_l 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((out_len + copy ) + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth copy sorted_l 0))
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((copy + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (copy + 1 )) ”
.

Definition anti_shuffle_safety_wit_43 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= cur_len)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= (out_len + copy ))) (PreH4 : (copy < cur_len)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 < cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : (0 <= copy)) (PreH15 : (copy <= cur_len)) (PreH16 : ((out_len + cur_len ) <= n)) (PreH17 : ((out_len + copy ) <= n)) (PreH18 : ((Zlength (out_sep_l)) = out_len)) (PreH19 : ((Zlength (sorted_l)) = cur_len)) (PreH20 : ((Zlength (cur_l)) = cur_len)) (PreH21 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH22 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH23 : (out_sep_relation_86 first out_l out_sep_l )) (PreH24 : (all_ascii sorted_l )) (PreH25 : (first = 1)) (PreH26 : (0 <= ch)) (PreH27 : (ch <= 127)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (problem_86_pre_z str_l )) (PreH31 : (anti_shuffle_safe_86 str_l )) (PreH32 : (anti_shuffle_commit_index_86 str_l i )) (PreH33 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH34 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH35 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full out ((out_len + copy ) + 1 ) (app (out_copy_l) ((cons ((signed_last_nbits ((Znth copy sorted_l 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((out_len + copy ) + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> (Znth copy sorted_l 0))
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_safety_wit_44 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (copy >= cur_len)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : (0 <= copy)) (PreH12 : (copy <= cur_len)) (PreH13 : ((out_len + cur_len ) <= n)) (PreH14 : ((out_len + copy ) <= n)) (PreH15 : ((Zlength (out_sep_l)) = out_len)) (PreH16 : ((Zlength (sorted_l)) = cur_len)) (PreH17 : ((Zlength (cur_l)) = cur_len)) (PreH18 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH19 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH20 : (out_sep_relation_86 first out_l out_sep_l )) (PreH21 : (all_ascii sorted_l )) (PreH22 : (first = 0)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (problem_86_pre_z str_l )) (PreH28 : (anti_shuffle_safe_86 str_l )) (PreH29 : (anti_shuffle_commit_index_86 str_l i )) (PreH30 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH31 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH32 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((out_len + cur_len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + cur_len )) ”
.

Definition anti_shuffle_safety_wit_45 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (copy >= cur_len)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : (0 <= copy)) (PreH12 : (copy <= cur_len)) (PreH13 : ((out_len + cur_len ) <= n)) (PreH14 : ((out_len + copy ) <= n)) (PreH15 : ((Zlength (out_sep_l)) = out_len)) (PreH16 : ((Zlength (sorted_l)) = cur_len)) (PreH17 : ((Zlength (cur_l)) = cur_len)) (PreH18 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH19 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH20 : (out_sep_relation_86 first out_l out_sep_l )) (PreH21 : (all_ascii sorted_l )) (PreH22 : (first = 1)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (problem_86_pre_z str_l )) (PreH28 : (anti_shuffle_safe_86 str_l )) (PreH29 : (anti_shuffle_commit_index_86 str_l i )) (PreH30 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH31 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH32 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "copy" ) )) # Int  |-> copy)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((out_len + cur_len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_len + cur_len )) ”
.

Definition anti_shuffle_safety_wit_46 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH11 : ((Zlength (sorted_l)) = cur_len)) (PreH12 : (out_next_l = (app (out_sep_l) (sorted_l)))) (PreH13 : ((Zlength (out_next_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (copy = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_47 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH11 : ((Zlength (sorted_l)) = cur_len)) (PreH12 : (out_next_l = (app (out_sep_l) (sorted_l)))) (PreH13 : ((Zlength (out_next_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (copy = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_48 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_sep_l)) = out_len)) (PreH10 : ((Zlength (sorted_l)) = 0)) (PreH11 : (out_next_l = out_sep_l)) (PreH12 : ((Zlength (out_next_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_49 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_sep_l)) = out_len)) (PreH10 : ((Zlength (sorted_l)) = 0)) (PreH11 : (out_next_l = out_sep_l)) (PreH12 : ((Zlength (out_next_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_50 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH11 : ((Zlength (sorted_l)) = cur_len)) (PreH12 : (out_next_l = (app (out_sep_l) (sorted_l)))) (PreH13 : ((Zlength (out_next_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (copy = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_51 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH11 : ((Zlength (sorted_l)) = cur_len)) (PreH12 : (out_next_l = (app (out_sep_l) (sorted_l)))) (PreH13 : ((Zlength (out_next_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (copy = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_52 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_sep_l)) = out_len)) (PreH10 : ((Zlength (sorted_l)) = 0)) (PreH11 : (out_next_l = out_sep_l)) (PreH12 : ((Zlength (out_next_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_53 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_sep_l)) = out_len)) (PreH10 : ((Zlength (sorted_l)) = 0)) (PreH11 : (out_next_l = out_sep_l)) (PreH12 : ((Zlength (out_next_l)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_54 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (1 <= cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l)) = out_len)) (PreH11 : ((Zlength (cur_l)) = cur_len)) (PreH12 : (first = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (problem_86_pre_z str_l )) (PreH18 : (anti_shuffle_safe_86 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (anti_shuffle_nonspace_step_86 str_l i first out_l cur_l ch )) (PreH21 : (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition anti_shuffle_safety_wit_55 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (1 <= cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l)) = out_len)) (PreH11 : ((Zlength (cur_l)) = cur_len)) (PreH12 : (first = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (problem_86_pre_z str_l )) (PreH18 : (anti_shuffle_safe_86 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (anti_shuffle_nonspace_step_86 str_l i first out_l cur_l ch )) (PreH21 : (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition anti_shuffle_safety_wit_56 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_next_l)) = out_len)) (PreH10 : (first = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_86_pre_z str_l )) (PreH16 : (anti_shuffle_safe_86 str_l )) (PreH17 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH18 : (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_next_l (@nil Z) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition anti_shuffle_safety_wit_57 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (out_len = n)) (PreH5 : (cur_len = 0)) (PreH6 : (first = 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : ((Zlength (out_l)) = out_len)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_86_pre_z str_l )) (PreH13 : (anti_shuffle_safe_86 str_l )) (PreH14 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH15 : (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l (@nil Z) )) (PreH16 : (anti_shuffle_final_86 str_l out_l )) (PreH17 : (problem_86_spec_z str_l out_l )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition anti_shuffle_safety_wit_58 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch_addr_v: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (out_len = n)) (PreH5 : (cur_len = 0)) (PreH6 : (first = 0)) (PreH7 : ((Zlength (out_l)) = out_len)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_86_pre_z str_l )) (PreH11 : (problem_86_spec_z str_l out_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition anti_shuffle_safety_wit_59 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch_addr_v: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (out_len = n)) (PreH5 : (cur_len = 0)) (PreH6 : (first = 0)) (PreH7 : ((Zlength (out_l)) = out_len)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_86_pre_z str_l )) (PreH11 : (problem_86_spec_z str_l out_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition anti_shuffle_entail_wit_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ ((Zlength (cur_l)) = 0) ” 
  &&  “ (1 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l 0 1 out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full retval_2 0 out_l )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
  **  (CharArray.full retval_3 0 cur_l )
  **  (CharArray.undef_seg retval_3 0 (retval + 1 ) ))
  ||
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ ((Zlength (cur_l)) = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l 0 1 out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full retval_2 0 out_l )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
  **  (CharArray.full retval_3 0 cur_l )
  **  (CharArray.undef_seg retval_3 0 (retval + 1 ) ))
.

Definition anti_shuffle_entail_wit_2_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l_2)) = cur_len)) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full cur (cur_len + 1 ) (app (cur_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (str_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 <= (cur_len + 1 )) ” 
  &&  “ ((cur_len + 1 ) <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = (cur_len + 1 )) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_nonspace_step_86 str_l i first out_l cur_l (Znth i (c_string (str_l)) 0) ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur (cur_len + 1 ) cur_l )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) ))
  ||
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 <= (cur_len + 1 )) ” 
  &&  “ ((cur_len + 1 ) <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = (cur_len + 1 )) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_nonspace_step_86 str_l i first out_l cur_l (Znth i (c_string (str_l)) 0) ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur (cur_len + 1 ) cur_l )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_2_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l_2)) = cur_len)) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full cur (cur_len + 1 ) (app (cur_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (str_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
|--
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 <= (cur_len + 1 )) ” 
  &&  “ ((cur_len + 1 ) <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = (cur_len + 1 )) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_nonspace_step_86 str_l i first out_l cur_l (Znth i (c_string (str_l)) 0) ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur (cur_len + 1 ) cur_l )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) ))
  ||
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 <= (cur_len + 1 )) ” 
  &&  “ ((cur_len + 1 ) <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = (cur_len + 1 )) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_nonspace_step_86 str_l i first out_l cur_l (Znth i (c_string (str_l)) 0) ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur (cur_len + 1 ) cur_l )
  **  (CharArray.undef_seg cur (cur_len + 1 ) (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_3_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (sorted_l_2: (@list Z)) (PreH1 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH2 : ((Zlength (sorted_l_2)) = cur_len)) (PreH3 : (all_ascii sorted_l_2 )) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (cur_len > 1)) (PreH6 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH7 : (i < n)) (PreH8 : (i <= n)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n + 1 ))) (PreH11 : (n = (string_length (str_l)))) (PreH12 : (out <> 0)) (PreH13 : (cur <> 0)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= n)) (PreH16 : (0 <= cur_len)) (PreH17 : (cur_len <= n)) (PreH18 : ((Zlength (out_l_2)) = out_len)) (PreH19 : ((Zlength (cur_l_2)) = cur_len)) (PreH20 : (first = 0)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (problem_86_pre_z str_l )) (PreH26 : (anti_shuffle_safe_86 str_l )) (PreH27 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH28 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_3_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (sorted_l_2: (@list Z)) (PreH1 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH2 : ((Zlength (sorted_l_2)) = cur_len)) (PreH3 : (all_ascii sorted_l_2 )) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (cur_len > 1)) (PreH6 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH7 : (i < n)) (PreH8 : (i <= n)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n + 1 ))) (PreH11 : (n = (string_length (str_l)))) (PreH12 : (out <> 0)) (PreH13 : (cur <> 0)) (PreH14 : (0 <= out_len)) (PreH15 : (out_len <= n)) (PreH16 : (0 <= cur_len)) (PreH17 : (cur_len <= n)) (PreH18 : ((Zlength (out_l_2)) = out_len)) (PreH19 : ((Zlength (cur_l_2)) = cur_len)) (PreH20 : (first = 1)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (problem_86_pre_z str_l )) (PreH26 : (anti_shuffle_safe_86 str_l )) (PreH27 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH28 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_3_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (sorted_l_2: (@list Z)) (PreH1 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH2 : ((Zlength (sorted_l_2)) = cur_len)) (PreH3 : (all_ascii sorted_l_2 )) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (cur_len > 1)) (PreH6 : (i >= n)) (PreH7 : (i <= n)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n + 1 ))) (PreH10 : (n = (string_length (str_l)))) (PreH11 : (out <> 0)) (PreH12 : (cur <> 0)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= n)) (PreH15 : (0 <= cur_len)) (PreH16 : (cur_len <= n)) (PreH17 : ((Zlength (out_l_2)) = out_len)) (PreH18 : ((Zlength (cur_l_2)) = cur_len)) (PreH19 : (first = 0)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_86_pre_z str_l )) (PreH25 : (anti_shuffle_safe_86 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_3_4 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (sorted_l_2: (@list Z)) (PreH1 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH2 : ((Zlength (sorted_l_2)) = cur_len)) (PreH3 : (all_ascii sorted_l_2 )) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (cur_len > 1)) (PreH6 : (i >= n)) (PreH7 : (i <= n)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n + 1 ))) (PreH10 : (n = (string_length (str_l)))) (PreH11 : (out <> 0)) (PreH12 : (cur <> 0)) (PreH13 : (0 <= out_len)) (PreH14 : (out_len <= n)) (PreH15 : (0 <= cur_len)) (PreH16 : (cur_len <= n)) (PreH17 : ((Zlength (out_l_2)) = out_len)) (PreH18 : ((Zlength (cur_l_2)) = cur_len)) (PreH19 : (first = 1)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_86_pre_z str_l )) (PreH25 : (anti_shuffle_safe_86 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_4_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len <= 1)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l_2)) = cur_len)) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_4_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len <= 1)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l_2)) = cur_len)) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_4_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len <= 1)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_4_4 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l_2: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len <= 1)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_5_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (first = 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= 1)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l_2)) = cur_len)) (PreH14 : (sorted_l_2 = cur_l_2)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_sep_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (1 <= (out_len + 1 )) ” 
  &&  “ ((out_len + 1 ) <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = ((out_len + 1 ) - 1 )) ” 
  &&  “ (out_sep_l = (app (out_l) ((cons (32) ((@nil Z)))))) ” 
  &&  “ ((Zlength (out_sep_l)) = (out_len + 1 )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) out_sep_l )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (first = 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= 1)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l_2)) = cur_len)) (PreH14 : (sorted_l_2 = cur_l_2)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  TT && emp 
|--
  EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ ((app (out_l_2) ((cons (32) ((@nil Z))))) = (app (out_l) ((cons (32) ((@nil Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (1 <= (out_len + 1 )) ” 
  &&  “ ((out_len + 1 ) <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = ((out_len + 1 ) - 1 )) ” 
  &&  “ ((Zlength ((app (out_l) ((cons (32) ((@nil Z))))))) = (out_len + 1 )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l_2)) = cur_len) ” 
  &&  “ (all_ascii sorted_l_2 ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  emp
).

Definition anti_shuffle_entail_wit_5_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (first = 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (1 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_sep_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (1 <= (out_len + 1 )) ” 
  &&  “ ((out_len + 1 ) <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = ((out_len + 1 ) - 1 )) ” 
  &&  “ (out_sep_l = (app (out_l) ((cons (32) ((@nil Z)))))) ” 
  &&  “ ((Zlength (out_sep_l)) = (out_len + 1 )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) out_sep_l )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (first = 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (1 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  TT && emp 
|--
  EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ ((app (out_l_2) ((cons (32) ((@nil Z))))) = (app (out_l) ((cons (32) ((@nil Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (1 <= (out_len + 1 )) ” 
  &&  “ ((out_len + 1 ) <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = ((out_len + 1 ) - 1 )) ” 
  &&  “ ((Zlength ((app (out_l) ((cons (32) ((@nil Z))))))) = (out_len + 1 )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l_2)) = cur_len) ” 
  &&  “ (all_ascii sorted_l_2 ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  emp
).

Definition anti_shuffle_entail_wit_6_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= 1)) (PreH11 : ((Zlength (out_l_2)) = out_len)) (PreH12 : ((Zlength (cur_l_2)) = cur_len)) (PreH13 : (sorted_l_2 = cur_l_2)) (PreH14 : ((Zlength (sorted_l_2)) = cur_len)) (PreH15 : (all_ascii sorted_l_2 )) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (anti_shuffle_commit_index_86 str_l i )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH26 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_sep_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (out_sep_l = out_l) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (first <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= 1)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l_2)) = cur_len)) (PreH14 : (sorted_l_2 = cur_l_2)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  TT && emp 
|--
  EX (cur_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l_2)) = out_len) ” 
  &&  “ ((Zlength (out_l_2)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l_2)) = cur_len) ” 
  &&  “ (all_ascii sorted_l_2 ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l ) ”
  &&  emp
).

Definition anti_shuffle_entail_wit_6_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (1 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l_2)) = out_len)) (PreH12 : ((Zlength (cur_l_2)) = cur_len)) (PreH13 : ((Zlength (sorted_l_2)) = cur_len)) (PreH14 : (all_ascii sorted_l_2 )) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH25 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (sorted_l: (@list Z))  (cur_l: (@list Z))  (out_sep_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (out_sep_l = out_l) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_entail_wit_7_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (cur_len > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (1 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l_2)) = (out_len - 1 ))) (PreH12 : (out_sep_l_2 = (app (out_l_2) ((cons (32) ((@nil Z))))))) (PreH13 : ((Zlength (out_sep_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + 0 ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + 0 )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l 0 out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 0 ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + 0 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + 0 ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + 0 )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l 0 out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 0 ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + 0 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_7_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (cur_len > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l_2)) = out_len)) (PreH12 : (out_sep_l_2 = out_l_2)) (PreH13 : ((Zlength (out_sep_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + 0 ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + 0 )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l 0 out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 0 ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + 0 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + 0 ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + 0 )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l 0 out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 0 ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + 0 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_8_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l_2: (@list Z)) (out_copy_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l: (@list Z)) (out_sep_l_2: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= cur_len)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= (out_len + copy ))) (PreH4 : (copy < cur_len)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 < cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : (0 <= copy)) (PreH15 : (copy <= cur_len)) (PreH16 : ((out_len + cur_len ) <= n)) (PreH17 : ((out_len + copy ) <= n)) (PreH18 : ((Zlength (out_sep_l_2)) = out_len)) (PreH19 : ((Zlength (sorted_l)) = cur_len)) (PreH20 : ((Zlength (cur_l_2)) = cur_len)) (PreH21 : ((Zlength (out_copy_l_2)) = (out_len + copy ))) (PreH22 : (copy_prefix_86 out_sep_l_2 sorted_l copy out_copy_l_2 )) (PreH23 : (out_sep_relation_86 first out_l_2 out_sep_l_2 )) (PreH24 : (all_ascii sorted_l )) (PreH25 : (first = 1)) (PreH26 : (0 <= ch)) (PreH27 : (ch <= 127)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (problem_86_pre_z str_l )) (PreH31 : (anti_shuffle_safe_86 str_l )) (PreH32 : (anti_shuffle_commit_index_86 str_l i )) (PreH33 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH34 : (sort_char_array_spec_86 cur_l_2 sorted_l )) (PreH35 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full out ((out_len + copy ) + 1 ) (app (out_copy_l_2) ((cons ((signed_last_nbits ((Znth copy sorted_l 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((out_len + copy ) + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l_2: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (1 <= (copy + 1 )) ” 
  &&  “ ((copy + 1 ) <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + (copy + 1 ) ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l_2)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + (copy + 1 ) )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l_2 (copy + 1 ) out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l_2 ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= (Znth copy sorted_l 0)) ” 
  &&  “ ((Znth copy sorted_l 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + (copy + 1 ) ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + (copy + 1 ) ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l_2: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (1 <= (copy + 1 )) ” 
  &&  “ ((copy + 1 ) <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + (copy + 1 ) ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l_2)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + (copy + 1 ) )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l_2 (copy + 1 ) out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l_2 ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= (Znth copy sorted_l 0)) ” 
  &&  “ ((Znth copy sorted_l 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + (copy + 1 ) ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + (copy + 1 ) ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_8_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l_2: (@list Z)) (out_copy_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l: (@list Z)) (out_sep_l_2: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= cur_len)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= (out_len + copy ))) (PreH4 : (copy < cur_len)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 < cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : (0 <= copy)) (PreH15 : (copy <= cur_len)) (PreH16 : ((out_len + cur_len ) <= n)) (PreH17 : ((out_len + copy ) <= n)) (PreH18 : ((Zlength (out_sep_l_2)) = out_len)) (PreH19 : ((Zlength (sorted_l)) = cur_len)) (PreH20 : ((Zlength (cur_l_2)) = cur_len)) (PreH21 : ((Zlength (out_copy_l_2)) = (out_len + copy ))) (PreH22 : (copy_prefix_86 out_sep_l_2 sorted_l copy out_copy_l_2 )) (PreH23 : (out_sep_relation_86 first out_l_2 out_sep_l_2 )) (PreH24 : (all_ascii sorted_l )) (PreH25 : (first = 0)) (PreH26 : (0 <= ch)) (PreH27 : (ch <= 127)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (problem_86_pre_z str_l )) (PreH31 : (anti_shuffle_safe_86 str_l )) (PreH32 : (anti_shuffle_commit_index_86 str_l i )) (PreH33 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH34 : (sort_char_array_spec_86 cur_l_2 sorted_l )) (PreH35 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (CharArray.full out ((out_len + copy ) + 1 ) (app (out_copy_l_2) ((cons ((signed_last_nbits ((Znth copy sorted_l 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((out_len + copy ) + 1 ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l_2: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (1 <= (copy + 1 )) ” 
  &&  “ ((copy + 1 ) <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + (copy + 1 ) ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l_2)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + (copy + 1 ) )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l_2 (copy + 1 ) out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l_2 ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= (Znth copy sorted_l 0)) ” 
  &&  “ ((Znth copy sorted_l 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + (copy + 1 ) ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + (copy + 1 ) ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l_2: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (1 <= (copy + 1 )) ” 
  &&  “ ((copy + 1 ) <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + (copy + 1 ) ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l_2)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + (copy + 1 ) )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l_2 (copy + 1 ) out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l_2 ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= (Znth copy sorted_l 0)) ” 
  &&  “ ((Znth copy sorted_l 0) <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + (copy + 1 ) ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + (copy + 1 ) ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_9_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (out_copy_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : (1 <= copy)) (PreH11 : (copy <= cur_len)) (PreH12 : ((out_len + cur_len ) <= n)) (PreH13 : ((out_len + copy ) <= n)) (PreH14 : ((Zlength (out_sep_l_2)) = out_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : ((Zlength (cur_l_2)) = cur_len)) (PreH17 : ((Zlength (out_copy_l_2)) = (out_len + copy ))) (PreH18 : (copy_prefix_86 out_sep_l_2 sorted_l_2 copy out_copy_l_2 )) (PreH19 : (out_sep_relation_86 first out_l_2 out_sep_l_2 )) (PreH20 : (all_ascii sorted_l_2 )) (PreH21 : (first = 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (problem_86_pre_z str_l )) (PreH27 : (anti_shuffle_safe_86 str_l )) (PreH28 : (anti_shuffle_commit_index_86 str_l i )) (PreH29 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH30 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH31 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l_2 )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_9_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (out_copy_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : (1 <= copy)) (PreH11 : (copy <= cur_len)) (PreH12 : ((out_len + cur_len ) <= n)) (PreH13 : ((out_len + copy ) <= n)) (PreH14 : ((Zlength (out_sep_l_2)) = out_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : ((Zlength (cur_l_2)) = cur_len)) (PreH17 : ((Zlength (out_copy_l_2)) = (out_len + copy ))) (PreH18 : (copy_prefix_86 out_sep_l_2 sorted_l_2 copy out_copy_l_2 )) (PreH19 : (out_sep_relation_86 first out_l_2 out_sep_l_2 )) (PreH20 : (all_ascii sorted_l_2 )) (PreH21 : (first = 1)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (problem_86_pre_z str_l )) (PreH27 : (anti_shuffle_safe_86 str_l )) (PreH28 : (anti_shuffle_commit_index_86 str_l i )) (PreH29 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH30 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH31 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l_2 )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (out_copy_l: (@list Z))  (cur_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_10_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l_2: (@list Z)) (out_copy_l: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (copy >= cur_len)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : (0 <= copy)) (PreH12 : (copy <= cur_len)) (PreH13 : ((out_len + cur_len ) <= n)) (PreH14 : ((out_len + copy ) <= n)) (PreH15 : ((Zlength (out_sep_l_2)) = out_len)) (PreH16 : ((Zlength (sorted_l_2)) = cur_len)) (PreH17 : ((Zlength (cur_l_2)) = cur_len)) (PreH18 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH19 : (copy_prefix_86 out_sep_l_2 sorted_l_2 copy out_copy_l )) (PreH20 : (out_sep_relation_86 first out_l_2 out_sep_l_2 )) (PreH21 : (all_ascii sorted_l_2 )) (PreH22 : (first = 1)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (problem_86_pre_z str_l )) (PreH28 : (anti_shuffle_safe_86 str_l )) (PreH29 : (anti_shuffle_commit_index_86 str_l i )) (PreH30 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH31 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH32 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= (out_len + cur_len )) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = ((out_len + cur_len ) - cur_len )) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (out_next_l = (app (out_sep_l) (sorted_l))) ” 
  &&  “ ((Zlength (out_next_l)) = (out_len + cur_len )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (copy = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + cur_len ) out_next_l )
  **  (CharArray.undef_seg out (out_len + cur_len ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= (out_len + cur_len )) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = ((out_len + cur_len ) - cur_len )) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (out_next_l = (app (out_sep_l) (sorted_l))) ” 
  &&  “ ((Zlength (out_next_l)) = (out_len + cur_len )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (copy = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + cur_len ) out_next_l )
  **  (CharArray.undef_seg out (out_len + cur_len ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_10_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l_2: (@list Z)) (out_copy_l: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (copy >= cur_len)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : (0 <= copy)) (PreH12 : (copy <= cur_len)) (PreH13 : ((out_len + cur_len ) <= n)) (PreH14 : ((out_len + copy ) <= n)) (PreH15 : ((Zlength (out_sep_l_2)) = out_len)) (PreH16 : ((Zlength (sorted_l_2)) = cur_len)) (PreH17 : ((Zlength (cur_l_2)) = cur_len)) (PreH18 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH19 : (copy_prefix_86 out_sep_l_2 sorted_l_2 copy out_copy_l )) (PreH20 : (out_sep_relation_86 first out_l_2 out_sep_l_2 )) (PreH21 : (all_ascii sorted_l_2 )) (PreH22 : (first = 0)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (problem_86_pre_z str_l )) (PreH28 : (anti_shuffle_safe_86 str_l )) (PreH29 : (anti_shuffle_commit_index_86 str_l i )) (PreH30 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH31 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH32 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= (out_len + cur_len )) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = ((out_len + cur_len ) - cur_len )) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (out_next_l = (app (out_sep_l) (sorted_l))) ” 
  &&  “ ((Zlength (out_next_l)) = (out_len + cur_len )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (copy = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + cur_len ) out_next_l )
  **  (CharArray.undef_seg out (out_len + cur_len ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= (out_len + cur_len )) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = ((out_len + cur_len ) - cur_len )) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (out_next_l = (app (out_sep_l) (sorted_l))) ” 
  &&  “ ((Zlength (out_next_l)) = (out_len + cur_len )) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (copy = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + cur_len ) out_next_l )
  **  (CharArray.undef_seg out (out_len + cur_len ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_11_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (cur_len <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l_2)) = out_len)) (PreH12 : (out_sep_l_2 = out_l_2)) (PreH13 : ((Zlength (out_sep_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = 0) ” 
  &&  “ (out_next_l = out_sep_l) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = 0) ” 
  &&  “ (out_next_l = out_sep_l) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_11_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (sorted_l_2: (@list Z)) (out_sep_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (cur_len <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (1 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l_2)) = (out_len - 1 ))) (PreH12 : (out_sep_l_2 = (app (out_l_2) ((cons (32) ((@nil Z))))))) (PreH13 : ((Zlength (out_sep_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l_2)) = cur_len)) (PreH15 : ((Zlength (sorted_l_2)) = cur_len)) (PreH16 : (all_ascii sorted_l_2 )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l_2 sorted_l_2 )) (PreH27 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_sep_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = 0) ” 
  &&  “ (out_next_l = out_sep_l) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (out_l: (@list Z))  (cur_l: (@list Z))  (out_next_l: (@list Z))  (sorted_l: (@list Z))  (out_sep_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = 0) ” 
  &&  “ (out_next_l = out_sep_l) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_12_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_sep_l)) = out_len)) (PreH10 : ((Zlength (sorted_l)) = 0)) (PreH11 : (out_next_l_2 = out_sep_l)) (PreH12 : ((Zlength (out_next_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH26 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_next_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur 0 (@nil Z) )
  **  (CharArray.undef_seg cur 0 (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (cur_len = 0)) (PreH11 : ((Zlength (out_sep_l)) = out_len)) (PreH12 : ((Zlength (sorted_l)) = 0)) (PreH13 : (out_next_l_2 = out_sep_l)) (PreH14 : ((Zlength (out_next_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
).

Definition anti_shuffle_entail_wit_12_1_split_goal_spatial := 
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (cur_len = 0)) (PreH11 : ((Zlength (out_sep_l)) = out_len)) (PreH12 : ((Zlength (sorted_l)) = 0)) (PreH13 : (out_next_l_2 = out_sep_l)) (PreH14 : ((Zlength (out_next_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
.

Definition anti_shuffle_entail_wit_12_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_sep_l)) = out_len)) (PreH10 : ((Zlength (sorted_l)) = 0)) (PreH11 : (out_next_l_2 = out_sep_l)) (PreH12 : ((Zlength (out_next_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH26 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_next_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur 0 (@nil Z) )
  **  (CharArray.undef_seg cur 0 (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (cur_len = 0)) (PreH11 : ((Zlength (out_sep_l)) = out_len)) (PreH12 : ((Zlength (sorted_l)) = 0)) (PreH13 : (out_next_l_2 = out_sep_l)) (PreH14 : ((Zlength (out_next_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
).

Definition anti_shuffle_entail_wit_12_2_split_goal_spatial := 
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (cur_len = 0)) (PreH11 : ((Zlength (out_sep_l)) = out_len)) (PreH12 : ((Zlength (sorted_l)) = 0)) (PreH13 : (out_next_l_2 = out_sep_l)) (PreH14 : ((Zlength (out_next_l_2)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
.

Definition anti_shuffle_entail_wit_12_3 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH11 : ((Zlength (sorted_l)) = cur_len)) (PreH12 : (out_next_l_2 = (app (out_sep_l) (sorted_l)))) (PreH13 : ((Zlength (out_next_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (copy = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_next_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur 0 (@nil Z) )
  **  (CharArray.undef_seg cur 0 (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 < cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (out_next_l_2 = (app (out_sep_l) (sorted_l)))) (PreH15 : ((Zlength (out_next_l_2)) = out_len)) (PreH16 : ((Zlength (cur_l)) = cur_len)) (PreH17 : (copy = cur_len)) (PreH18 : (all_ascii sorted_l )) (PreH19 : (first = 0)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_86_pre_z str_l )) (PreH25 : (anti_shuffle_safe_86 str_l )) (PreH26 : (anti_shuffle_commit_index_86 str_l i )) (PreH27 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH28 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH29 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH30 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
).

Definition anti_shuffle_entail_wit_12_3_split_goal_spatial := 
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 < cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (out_next_l_2 = (app (out_sep_l) (sorted_l)))) (PreH15 : ((Zlength (out_next_l_2)) = out_len)) (PreH16 : ((Zlength (cur_l)) = cur_len)) (PreH17 : (copy = cur_len)) (PreH18 : (all_ascii sorted_l )) (PreH19 : (first = 0)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_86_pre_z str_l )) (PreH25 : (anti_shuffle_safe_86 str_l )) (PreH26 : (anti_shuffle_commit_index_86 str_l i )) (PreH27 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH28 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH29 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH30 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
.

Definition anti_shuffle_entail_wit_12_4 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (0 < cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH11 : ((Zlength (sorted_l)) = cur_len)) (PreH12 : (out_next_l_2 = (app (out_sep_l) (sorted_l)))) (PreH13 : ((Zlength (out_next_l_2)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (copy = cur_len)) (PreH16 : (all_ascii sorted_l )) (PreH17 : (first = 1)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (anti_shuffle_safe_86 str_l )) (PreH24 : (anti_shuffle_commit_index_86 str_l i )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH27 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH28 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_next_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (out_next_l)) = out_len) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l (@nil Z) ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur 0 (@nil Z) )
  **  (CharArray.undef_seg cur 0 (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 < cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (out_next_l_2 = (app (out_sep_l) (sorted_l)))) (PreH15 : ((Zlength (out_next_l_2)) = out_len)) (PreH16 : ((Zlength (cur_l)) = cur_len)) (PreH17 : (copy = cur_len)) (PreH18 : (all_ascii sorted_l )) (PreH19 : (first = 1)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_86_pre_z str_l )) (PreH25 : (anti_shuffle_safe_86 str_l )) (PreH26 : (anti_shuffle_commit_index_86 str_l i )) (PreH27 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH28 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH29 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH30 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
).

Definition anti_shuffle_entail_wit_12_4_split_goal_spatial := 
forall (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (out_next_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (copy: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 < cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_sep_l)) = (out_len - cur_len ))) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (out_next_l_2 = (app (out_sep_l) (sorted_l)))) (PreH15 : ((Zlength (out_next_l_2)) = out_len)) (PreH16 : ((Zlength (cur_l)) = cur_len)) (PreH17 : (copy = cur_len)) (PreH18 : (all_ascii sorted_l )) (PreH19 : (first = 1)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_86_pre_z str_l )) (PreH25 : (anti_shuffle_safe_86 str_l )) (PreH26 : (anti_shuffle_commit_index_86 str_l i )) (PreH27 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH28 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH29 : (anti_shuffle_commit_step_86 str_l i first out_l cur_l out_next_l_2 )) (PreH30 : (anti_shuffle_scan_state_86 str_l (i + 1 ) 0 out_next_l_2 (@nil Z) )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (CharArray.undef_full cur (n + 1 ) )
.

Definition anti_shuffle_entail_wit_13_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (1 <= cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l_2)) = out_len)) (PreH11 : ((Zlength (cur_l_2)) = cur_len)) (PreH12 : (first = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (problem_86_pre_z str_l )) (PreH18 : (anti_shuffle_safe_86 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (anti_shuffle_nonspace_step_86 str_l i first out_l_2 cur_l_2 ch )) (PreH21 : (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_13_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (cur_l_2: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (1 <= cur_len)) (PreH9 : (cur_len <= n)) (PreH10 : ((Zlength (out_l_2)) = out_len)) (PreH11 : ((Zlength (cur_l_2)) = cur_len)) (PreH12 : (first = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (problem_86_pre_z str_l )) (PreH18 : (anti_shuffle_safe_86 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (anti_shuffle_nonspace_step_86 str_l i first out_l_2 cur_l_2 ch )) (PreH21 : (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l_2 cur_l_2 )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l_2 )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_13_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_next_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (0 <= out_len)) (PreH7 : (out_len <= n)) (PreH8 : (cur_len = 0)) (PreH9 : ((Zlength (out_next_l)) = out_len)) (PreH10 : (first = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_86_pre_z str_l )) (PreH16 : (anti_shuffle_safe_86 str_l )) (PreH17 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH18 : (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_next_l (@nil Z) )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_next_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
  ||
  (EX (cur_l: (@list Z))  (out_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (i + 1 ) first out_l cur_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) ))
.

Definition anti_shuffle_entail_wit_14_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i > n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n + 1 ))) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l_2)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : (first = 1)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (problem_86_pre_z str_l )) (PreH19 : (anti_shuffle_safe_86 str_l )) (PreH20 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH21 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l (@nil Z) ) ” 
  &&  “ (anti_shuffle_final_86 str_l out_l ) ” 
  &&  “ (problem_86_spec_z str_l out_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (cur_l = (@nil Z)) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((Zlength (out_l_2)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l_2 (@nil Z) ) ” 
  &&  “ (anti_shuffle_final_86 str_l out_l_2 ) ” 
  &&  “ (problem_86_spec_z str_l out_l_2 ) ”
  &&  emp
).

Definition anti_shuffle_entail_wit_14_1_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (cur_l = (@nil Z)) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (n = (string_length (str_l))) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_3 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (out <> 0) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_4 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (cur <> 0) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_5 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (out_len = n) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_6 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (cur_len = 0) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_7 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (first = 0) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_8 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (0 <= ch) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_9 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (ch <= 127) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_10 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ ((Zlength (out_l_2)) = out_len) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_11 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (valid_string str_l ) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_12 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (all_ascii str_l ) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_13 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (problem_86_pre_z str_l ) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_14 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (anti_shuffle_safe_86 str_l ) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_15 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_16 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l_2 (@nil Z) ) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_17 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (anti_shuffle_final_86 str_l out_l_2 ) ”
.

Definition anti_shuffle_entail_wit_14_1_split_goal_18 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (problem_86_spec_z str_l out_l_2 ) ”
.

Definition anti_shuffle_entail_wit_14_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i > n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n + 1 ))) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l_2)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : (first = 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (problem_86_pre_z str_l )) (PreH19 : (anti_shuffle_safe_86 str_l )) (PreH20 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH21 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l (@nil Z) ) ” 
  &&  “ (anti_shuffle_final_86 str_l out_l ) ” 
  &&  “ (problem_86_spec_z str_l out_l ) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (problem_86_spec_z str_l out_l_2 ) ” 
  &&  “ (anti_shuffle_final_86 str_l out_l_2 ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l_2 (@nil Z) ) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_l = (@nil Z)) ”
  &&  emp
).

Definition anti_shuffle_entail_wit_14_2_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (problem_86_spec_z str_l out_l_2 ) ”
.

Definition anti_shuffle_entail_wit_14_2_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (anti_shuffle_final_86 str_l out_l_2 ) ”
.

Definition anti_shuffle_entail_wit_14_2_split_goal_3 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l_2 (@nil Z) ) ”
.

Definition anti_shuffle_entail_wit_14_2_split_goal_4 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (cur_len = 0) ”
.

Definition anti_shuffle_entail_wit_14_2_split_goal_5 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (out_len = n) ”
.

Definition anti_shuffle_entail_wit_14_2_split_goal_6 := 
forall (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l_2: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (cur <> 0)) (PreH8 : (0 <= out_len)) (PreH9 : (out_len <= n)) (PreH10 : (0 <= cur_len)) (PreH11 : (cur_len <= n)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : ((Zlength (cur_l)) = cur_len)) (PreH14 : (first = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_86_pre_z str_l )) (PreH20 : (anti_shuffle_safe_86 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (anti_shuffle_scan_state_86 str_l i first out_l_2 cur_l )) ,
  TT && emp 
|--
  “ (cur_l = (@nil Z)) ”
.

Definition anti_shuffle_entail_wit_15 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= out_len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (out_len = n)) (PreH8 : (cur_len = 0)) (PreH9 : (first = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_86_pre_z str_l )) (PreH16 : (anti_shuffle_safe_86 str_l )) (PreH17 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH18 : (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l_2 (@nil Z) )) (PreH19 : (anti_shuffle_final_86 str_l out_l_2 )) (PreH20 : (problem_86_spec_z str_l out_l_2 )) ,
  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (problem_86_spec_z str_l out_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (out_l_2: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= cur_len)) (PreH3 : (0 <= out_len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (out_len = n)) (PreH8 : (cur_len = 0)) (PreH9 : (first = 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : ((Zlength (out_l_2)) = out_len)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_86_pre_z str_l )) (PreH16 : (anti_shuffle_safe_86 str_l )) (PreH17 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH18 : (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l_2 (@nil Z) )) (PreH19 : (anti_shuffle_final_86 str_l out_l_2 )) (PreH20 : (problem_86_spec_z str_l out_l_2 )) ,
  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((app (out_l_2) ((cons (0) ((@nil Z))))) = (app (out_l) ((cons (0) ((@nil Z)))))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (problem_86_spec_z str_l out_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.undef_full cur (n + 1 ) )
).

Definition anti_shuffle_entail_wit_16 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (out_len + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (cur <> 0)) (PreH6 : (out_len = n)) (PreH7 : (cur_len = 0)) (PreH8 : (first = 0)) (PreH9 : ((Zlength (out_l_2)) = out_len)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_86_pre_z str_l )) (PreH13 : (problem_86_spec_z str_l out_l_2 )) (PreH14 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_spec_z str_l out_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
.

Definition anti_shuffle_return_wit_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l_2: (@list Z)) (n: Z) (out: Z) (out_len: Z) (cur_len: Z) (first: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (out_len = n)) (PreH4 : (cur_len = 0)) (PreH5 : (first = 0)) (PreH6 : ((Zlength (out_l_2)) = out_len)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (problem_86_spec_z str_l out_l_2 )) (PreH10 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_86_spec_z str_l out_l ) ” 
  &&  “ ((Zlength (out_l)) = (string_length (str_l))) ”
  &&  (CharArray.full out ((string_length (str_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (store_string s_pre str_l )
) \/
(
forall (str_l: (@list Z)) (out_l_2: (@list Z)) (n: Z) (out: Z) (out_len: Z) (cur_len: Z) (first: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (out_len + 1 ))) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (out_len = n)) (PreH6 : (cur_len = 0)) (PreH7 : (first = 0)) (PreH8 : ((Zlength (out_l_2)) = out_len)) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (problem_86_spec_z str_l out_l_2 )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_86_spec_z str_l out_l ) ” 
  &&  “ ((Zlength (out_l)) = (string_length (str_l))) ”
  &&  (CharArray.full out ((string_length (str_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
).

Definition anti_shuffle_partial_solve_wit_1_pure := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_86_pre_z str_l )) (PreH4 : (anti_shuffle_safe_86 str_l )) (PreH5 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition anti_shuffle_partial_solve_wit_1_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_86_pre_z str_l )) (PreH4 : (anti_shuffle_safe_86 str_l )) (PreH5 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (store_string s_pre str_l )
.

Definition anti_shuffle_partial_solve_wit_1 := anti_shuffle_partial_solve_wit_1_pure -> anti_shuffle_partial_solve_wit_1_aux.

Definition anti_shuffle_partial_solve_wit_2_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_86_pre_z str_l )) (PreH6 : (anti_shuffle_safe_86 str_l )) (PreH7 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  (store_string s_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition anti_shuffle_partial_solve_wit_2_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_86_pre_z str_l )) (PreH8 : (anti_shuffle_safe_86 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition anti_shuffle_partial_solve_wit_2_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_86_pre_z str_l )) (PreH6 : (anti_shuffle_safe_86 str_l )) (PreH7 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre str_l )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition anti_shuffle_partial_solve_wit_2 := anti_shuffle_partial_solve_wit_2_pure -> anti_shuffle_partial_solve_wit_2_aux.

Definition anti_shuffle_partial_solve_wit_3_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_86_pre_z str_l )) (PreH7 : (anti_shuffle_safe_86 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (problem_86_pre_z str_l )) (PreH9 : (anti_shuffle_safe_86 str_l )) (PreH10 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition anti_shuffle_partial_solve_wit_3_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (problem_86_pre_z str_l )) (PreH9 : (anti_shuffle_safe_86 str_l )) (PreH10 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition anti_shuffle_partial_solve_wit_3_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_86_pre_z str_l )) (PreH7 : (anti_shuffle_safe_86 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition anti_shuffle_partial_solve_wit_3 := anti_shuffle_partial_solve_wit_3_pure -> anti_shuffle_partial_solve_wit_3_aux.

Definition anti_shuffle_partial_solve_wit_4 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((cur + (cur_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i cur cur_len cur_len (n + 1 ) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
.

Definition anti_shuffle_partial_solve_wit_5 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((cur + (cur_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i cur cur_len cur_len (n + 1 ) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
.

Definition anti_shuffle_partial_solve_wit_6_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : (i >= n)) (PreH16 : (i <= n)) (PreH17 : (0 <= i)) (PreH18 : (i <= (n + 1 ))) (PreH19 : (n = (string_length (str_l)))) (PreH20 : (out <> 0)) (PreH21 : (cur <> 0)) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= n)) (PreH24 : (0 <= cur_len)) (PreH25 : (cur_len <= n)) (PreH26 : ((Zlength (out_l)) = out_len)) (PreH27 : ((Zlength (cur_l)) = cur_len)) (PreH28 : (first = 1)) (PreH29 : (0 <= ch)) (PreH30 : (ch <= 127)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (problem_86_pre_z str_l )) (PreH34 : (anti_shuffle_safe_86 str_l )) (PreH35 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH36 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
).

Definition anti_shuffle_partial_solve_wit_6_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : (i >= n)) (PreH16 : (i <= n)) (PreH17 : (0 <= i)) (PreH18 : (i <= (n + 1 ))) (PreH19 : (n = (string_length (str_l)))) (PreH20 : (out <> 0)) (PreH21 : (cur <> 0)) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= n)) (PreH24 : (0 <= cur_len)) (PreH25 : (cur_len <= n)) (PreH26 : ((Zlength (out_l)) = out_len)) (PreH27 : ((Zlength (cur_l)) = cur_len)) (PreH28 : (first = 1)) (PreH29 : (0 <= ch)) (PreH30 : (ch <= 127)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (problem_86_pre_z str_l )) (PreH34 : (anti_shuffle_safe_86 str_l )) (PreH35 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH36 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
.

Definition anti_shuffle_partial_solve_wit_6_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (cur_len > 1) ” 
  &&  “ (i >= n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (CharArray.full cur cur_len cur_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_6 := anti_shuffle_partial_solve_wit_6_pure -> anti_shuffle_partial_solve_wit_6_aux.

Definition anti_shuffle_partial_solve_wit_7_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : (i >= n)) (PreH16 : (i <= n)) (PreH17 : (0 <= i)) (PreH18 : (i <= (n + 1 ))) (PreH19 : (n = (string_length (str_l)))) (PreH20 : (out <> 0)) (PreH21 : (cur <> 0)) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= n)) (PreH24 : (0 <= cur_len)) (PreH25 : (cur_len <= n)) (PreH26 : ((Zlength (out_l)) = out_len)) (PreH27 : ((Zlength (cur_l)) = cur_len)) (PreH28 : (first = 0)) (PreH29 : (0 <= ch)) (PreH30 : (ch <= 127)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (problem_86_pre_z str_l )) (PreH34 : (anti_shuffle_safe_86 str_l )) (PreH35 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH36 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
).

Definition anti_shuffle_partial_solve_wit_7_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : (i >= n)) (PreH16 : (i <= n)) (PreH17 : (0 <= i)) (PreH18 : (i <= (n + 1 ))) (PreH19 : (n = (string_length (str_l)))) (PreH20 : (out <> 0)) (PreH21 : (cur <> 0)) (PreH22 : (0 <= out_len)) (PreH23 : (out_len <= n)) (PreH24 : (0 <= cur_len)) (PreH25 : (cur_len <= n)) (PreH26 : ((Zlength (out_l)) = out_len)) (PreH27 : ((Zlength (cur_l)) = cur_len)) (PreH28 : (first = 0)) (PreH29 : (0 <= ch)) (PreH30 : (ch <= 127)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (problem_86_pre_z str_l )) (PreH34 : (anti_shuffle_safe_86 str_l )) (PreH35 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH36 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
.

Definition anti_shuffle_partial_solve_wit_7_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 <= cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : ((Zlength (out_l)) = out_len)) (PreH14 : ((Zlength (cur_l)) = cur_len)) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (cur_len > 1) ” 
  &&  “ (i >= n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (CharArray.full cur cur_len cur_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_7 := anti_shuffle_partial_solve_wit_7_pure -> anti_shuffle_partial_solve_wit_7_aux.

Definition anti_shuffle_partial_solve_wit_8_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH16 : (i < n)) (PreH17 : (i <= n)) (PreH18 : (0 <= i)) (PreH19 : (i <= (n + 1 ))) (PreH20 : (n = (string_length (str_l)))) (PreH21 : (out <> 0)) (PreH22 : (cur <> 0)) (PreH23 : (0 <= out_len)) (PreH24 : (out_len <= n)) (PreH25 : (0 <= cur_len)) (PreH26 : (cur_len <= n)) (PreH27 : ((Zlength (out_l)) = out_len)) (PreH28 : ((Zlength (cur_l)) = cur_len)) (PreH29 : (first = 1)) (PreH30 : (0 <= ch)) (PreH31 : (ch <= 127)) (PreH32 : (valid_string str_l )) (PreH33 : (all_ascii str_l )) (PreH34 : (problem_86_pre_z str_l )) (PreH35 : (anti_shuffle_safe_86 str_l )) (PreH36 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH37 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
).

Definition anti_shuffle_partial_solve_wit_8_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH16 : (i < n)) (PreH17 : (i <= n)) (PreH18 : (0 <= i)) (PreH19 : (i <= (n + 1 ))) (PreH20 : (n = (string_length (str_l)))) (PreH21 : (out <> 0)) (PreH22 : (cur <> 0)) (PreH23 : (0 <= out_len)) (PreH24 : (out_len <= n)) (PreH25 : (0 <= cur_len)) (PreH26 : (cur_len <= n)) (PreH27 : ((Zlength (out_l)) = out_len)) (PreH28 : ((Zlength (cur_l)) = cur_len)) (PreH29 : (first = 1)) (PreH30 : (0 <= ch)) (PreH31 : (ch <= 127)) (PreH32 : (valid_string str_l )) (PreH33 : (all_ascii str_l )) (PreH34 : (problem_86_pre_z str_l )) (PreH35 : (anti_shuffle_safe_86 str_l )) (PreH36 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH37 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
.

Definition anti_shuffle_partial_solve_wit_8_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 1)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (cur_len > 1) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ” 
  &&  “ (i < n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (CharArray.full cur cur_len cur_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_8 := anti_shuffle_partial_solve_wit_8_pure -> anti_shuffle_partial_solve_wit_8_aux.

Definition anti_shuffle_partial_solve_wit_9_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH16 : (i < n)) (PreH17 : (i <= n)) (PreH18 : (0 <= i)) (PreH19 : (i <= (n + 1 ))) (PreH20 : (n = (string_length (str_l)))) (PreH21 : (out <> 0)) (PreH22 : (cur <> 0)) (PreH23 : (0 <= out_len)) (PreH24 : (out_len <= n)) (PreH25 : (0 <= cur_len)) (PreH26 : (cur_len <= n)) (PreH27 : ((Zlength (out_l)) = out_len)) (PreH28 : ((Zlength (cur_l)) = cur_len)) (PreH29 : (first = 0)) (PreH30 : (0 <= ch)) (PreH31 : (ch <= 127)) (PreH32 : (valid_string str_l )) (PreH33 : (all_ascii str_l )) (PreH34 : (problem_86_pre_z str_l )) (PreH35 : (anti_shuffle_safe_86 str_l )) (PreH36 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH37 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
).

Definition anti_shuffle_partial_solve_wit_9_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (ch <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (ch >= INT_MIN)) (PreH8 : (first >= INT_MIN)) (PreH9 : (cur_len >= INT_MIN)) (PreH10 : (out_len >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (str_l)) + 1 ))) (PreH14 : (cur_len > 1)) (PreH15 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH16 : (i < n)) (PreH17 : (i <= n)) (PreH18 : (0 <= i)) (PreH19 : (i <= (n + 1 ))) (PreH20 : (n = (string_length (str_l)))) (PreH21 : (out <> 0)) (PreH22 : (cur <> 0)) (PreH23 : (0 <= out_len)) (PreH24 : (out_len <= n)) (PreH25 : (0 <= cur_len)) (PreH26 : (cur_len <= n)) (PreH27 : ((Zlength (out_l)) = out_len)) (PreH28 : ((Zlength (cur_l)) = cur_len)) (PreH29 : (first = 0)) (PreH30 : (0 <= ch)) (PreH31 : (ch <= 127)) (PreH32 : (valid_string str_l )) (PreH33 : (all_ascii str_l )) (PreH34 : (problem_86_pre_z str_l )) (PreH35 : (anti_shuffle_safe_86 str_l )) (PreH36 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH37 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (all_ascii cur_l ) ”
.

Definition anti_shuffle_partial_solve_wit_9_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (cur_l: (@list Z)) (out_l: (@list Z)) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (cur_len > 1)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (cur <> 0)) (PreH10 : (0 <= out_len)) (PreH11 : (out_len <= n)) (PreH12 : (0 <= cur_len)) (PreH13 : (cur_len <= n)) (PreH14 : ((Zlength (out_l)) = out_len)) (PreH15 : ((Zlength (cur_l)) = cur_len)) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len cur_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len < INT_MAX) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (all_ascii cur_l ) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (cur_len > 1) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ” 
  &&  “ (i < n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (CharArray.full cur cur_len cur_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_9 := anti_shuffle_partial_solve_wit_9_pure -> anti_shuffle_partial_solve_wit_9_aux.

Definition anti_shuffle_partial_solve_wit_10 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (1 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : ((Zlength (sorted_l)) = cur_len)) (PreH14 : (all_ascii sorted_l )) (PreH15 : (first = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_86_pre_z str_l )) (PreH21 : (anti_shuffle_safe_86 str_l )) (PreH22 : (anti_shuffle_commit_index_86 str_l i )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH25 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (1 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i out out_len out_len (n + 1 ) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_11 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (i: Z) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (first = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 <= cur_len)) (PreH10 : (cur_len <= 1)) (PreH11 : ((Zlength (out_l)) = out_len)) (PreH12 : ((Zlength (cur_l)) = cur_len)) (PreH13 : (sorted_l = cur_l)) (PreH14 : ((Zlength (sorted_l)) = cur_len)) (PreH15 : (all_ascii sorted_l )) (PreH16 : (first = 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_86_pre_z str_l )) (PreH22 : (anti_shuffle_safe_86 str_l )) (PreH23 : (anti_shuffle_commit_index_86 str_l i )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH26 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (cur_len <= 1) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ (sorted_l = cur_l) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i out out_len out_len (n + 1 ) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_12 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (copy < cur_len)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : (0 <= copy)) (PreH12 : (copy <= cur_len)) (PreH13 : ((out_len + cur_len ) <= n)) (PreH14 : ((out_len + copy ) <= n)) (PreH15 : ((Zlength (out_sep_l)) = out_len)) (PreH16 : ((Zlength (sorted_l)) = cur_len)) (PreH17 : ((Zlength (cur_l)) = cur_len)) (PreH18 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH19 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH20 : (out_sep_relation_86 first out_l out_sep_l )) (PreH21 : (all_ascii sorted_l )) (PreH22 : (first = 0)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (problem_86_pre_z str_l )) (PreH28 : (anti_shuffle_safe_86 str_l )) (PreH29 : (anti_shuffle_commit_index_86 str_l i )) (PreH30 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH31 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH32 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (out_len + copy )) ” 
  &&  “ (copy < cur_len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((cur + (copy * sizeof(CHAR) ) )) # Char  |-> (Znth copy sorted_l 0))
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.missing_i cur copy 0 cur_len sorted_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_13 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (copy < cur_len)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (cur <> 0)) (PreH7 : (0 <= out_len)) (PreH8 : (out_len <= n)) (PreH9 : (0 < cur_len)) (PreH10 : (cur_len <= n)) (PreH11 : (0 <= copy)) (PreH12 : (copy <= cur_len)) (PreH13 : ((out_len + cur_len ) <= n)) (PreH14 : ((out_len + copy ) <= n)) (PreH15 : ((Zlength (out_sep_l)) = out_len)) (PreH16 : ((Zlength (sorted_l)) = cur_len)) (PreH17 : ((Zlength (cur_l)) = cur_len)) (PreH18 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH19 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH20 : (out_sep_relation_86 first out_l out_sep_l )) (PreH21 : (all_ascii sorted_l )) (PreH22 : (first = 1)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (problem_86_pre_z str_l )) (PreH28 : (anti_shuffle_safe_86 str_l )) (PreH29 : (anti_shuffle_commit_index_86 str_l i )) (PreH30 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH31 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH32 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (out_len + copy )) ” 
  &&  “ (copy < cur_len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((cur + (copy * sizeof(CHAR) ) )) # Char  |-> (Znth copy sorted_l 0))
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.missing_i cur copy 0 cur_len sorted_l )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_14 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (out_len + copy ))) (PreH3 : (copy < cur_len)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : (0 <= copy)) (PreH14 : (copy <= cur_len)) (PreH15 : ((out_len + cur_len ) <= n)) (PreH16 : ((out_len + copy ) <= n)) (PreH17 : ((Zlength (out_sep_l)) = out_len)) (PreH18 : ((Zlength (sorted_l)) = cur_len)) (PreH19 : ((Zlength (cur_l)) = cur_len)) (PreH20 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH21 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH22 : (out_sep_relation_86 first out_l out_sep_l )) (PreH23 : (all_ascii sorted_l )) (PreH24 : (first = 0)) (PreH25 : (0 <= ch)) (PreH26 : (ch <= 127)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (problem_86_pre_z str_l )) (PreH30 : (anti_shuffle_safe_86 str_l )) (PreH31 : (anti_shuffle_commit_index_86 str_l i )) (PreH32 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH33 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH34 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= cur_len) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (out_len + copy )) ” 
  &&  “ (copy < cur_len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((out + ((out_len + copy ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (out_len + copy ) (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_15 := 
forall (s_pre: Z) (str_l: (@list Z)) (ch: Z) (first: Z) (out_l: (@list Z)) (out_copy_l: (@list Z)) (cur_l: (@list Z)) (sorted_l: (@list Z)) (out_sep_l: (@list Z)) (copy: Z) (cur_len: Z) (out_len: Z) (cur: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (out_len + copy ))) (PreH3 : (copy < cur_len)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (cur <> 0)) (PreH9 : (0 <= out_len)) (PreH10 : (out_len <= n)) (PreH11 : (0 < cur_len)) (PreH12 : (cur_len <= n)) (PreH13 : (0 <= copy)) (PreH14 : (copy <= cur_len)) (PreH15 : ((out_len + cur_len ) <= n)) (PreH16 : ((out_len + copy ) <= n)) (PreH17 : ((Zlength (out_sep_l)) = out_len)) (PreH18 : ((Zlength (sorted_l)) = cur_len)) (PreH19 : ((Zlength (cur_l)) = cur_len)) (PreH20 : ((Zlength (out_copy_l)) = (out_len + copy ))) (PreH21 : (copy_prefix_86 out_sep_l sorted_l copy out_copy_l )) (PreH22 : (out_sep_relation_86 first out_l out_sep_l )) (PreH23 : (all_ascii sorted_l )) (PreH24 : (first = 1)) (PreH25 : (0 <= ch)) (PreH26 : (ch <= 127)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (problem_86_pre_z str_l )) (PreH30 : (anti_shuffle_safe_86 str_l )) (PreH31 : (anti_shuffle_commit_index_86 str_l i )) (PreH32 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH33 : (sort_char_array_spec_86 cur_l sorted_l )) (PreH34 : (anti_shuffle_scan_state_86 str_l i first out_l cur_l )) ,
  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg out (out_len + copy ) (n + 1 ) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= cur_len) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (out_len + copy )) ” 
  &&  “ (copy < cur_len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= n) ” 
  &&  “ (0 < cur_len) ” 
  &&  “ (cur_len <= n) ” 
  &&  “ (0 <= copy) ” 
  &&  “ (copy <= cur_len) ” 
  &&  “ ((out_len + cur_len ) <= n) ” 
  &&  “ ((out_len + copy ) <= n) ” 
  &&  “ ((Zlength (out_sep_l)) = out_len) ” 
  &&  “ ((Zlength (sorted_l)) = cur_len) ” 
  &&  “ ((Zlength (cur_l)) = cur_len) ” 
  &&  “ ((Zlength (out_copy_l)) = (out_len + copy )) ” 
  &&  “ (copy_prefix_86 out_sep_l sorted_l copy out_copy_l ) ” 
  &&  “ (out_sep_relation_86 first out_l out_sep_l ) ” 
  &&  “ (all_ascii sorted_l ) ” 
  &&  “ (first = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (anti_shuffle_commit_index_86 str_l i ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (sort_char_array_spec_86 cur_l sorted_l ) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l i first out_l cur_l ) ”
  &&  (((out + ((out_len + copy ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (out_len + copy ) (out_len + copy ) (n + 1 ) )
  **  (CharArray.full cur cur_len sorted_l )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out (out_len + copy ) out_copy_l )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_16 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (out_len = n)) (PreH5 : (cur_len = 0)) (PreH6 : (first = 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : ((Zlength (out_l)) = out_len)) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (problem_86_pre_z str_l )) (PreH13 : (anti_shuffle_safe_86 str_l )) (PreH14 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH15 : (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l (@nil Z) )) (PreH16 : (anti_shuffle_final_86 str_l out_l )) (PreH17 : (problem_86_spec_z str_l out_l )) ,
  (store_string s_pre str_l )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (n + 1 ) )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= cur_len) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (anti_shuffle_safe_86 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (anti_shuffle_scan_state_86 str_l (n + 1 ) first out_l (@nil Z) ) ” 
  &&  “ (anti_shuffle_final_86 str_l out_l ) ” 
  &&  “ (problem_86_spec_z str_l out_l ) ”
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i out out_len out_len (n + 1 ) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.full cur cur_len (@nil Z) )
  **  (CharArray.undef_seg cur cur_len (n + 1 ) )
.

Definition anti_shuffle_partial_solve_wit_17_pure := 
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch_addr_v: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (out_len = n)) (PreH5 : (cur_len = 0)) (PreH6 : (first = 0)) (PreH7 : ((Zlength (out_l)) = out_len)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_86_pre_z str_l )) (PreH11 : (problem_86_spec_z str_l out_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 < (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((string_length (str_l)) + 1 )) ”
) \/
(
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch_addr_v: Z) (PreH1 : (ch_addr_v <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (ch_addr_v >= INT_MIN)) (PreH7 : (first >= INT_MIN)) (PreH8 : (cur_len >= INT_MIN)) (PreH9 : (out_len >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (0 <= ((string_length (str_l)) + 1 ))) (PreH12 : (0 <= (out_len + 1 ))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (out <> 0)) (PreH15 : (cur <> 0)) (PreH16 : (out_len = n)) (PreH17 : (cur_len = 0)) (PreH18 : (first = 0)) (PreH19 : ((Zlength (out_l)) = out_len)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (problem_86_spec_z str_l out_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
|--
  “ (0 < ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 < (n + 1 )) ”
).

Definition anti_shuffle_partial_solve_wit_17_pure_split_goal_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch_addr_v: Z) (PreH1 : (ch_addr_v <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (ch_addr_v >= INT_MIN)) (PreH7 : (first >= INT_MIN)) (PreH8 : (cur_len >= INT_MIN)) (PreH9 : (out_len >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (0 <= ((string_length (str_l)) + 1 ))) (PreH12 : (0 <= (out_len + 1 ))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (out <> 0)) (PreH15 : (cur <> 0)) (PreH16 : (out_len = n)) (PreH17 : (cur_len = 0)) (PreH18 : (first = 0)) (PreH19 : ((Zlength (out_l)) = out_len)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (problem_86_spec_z str_l out_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
|--
  “ (0 < ((string_length (str_l)) + 1 )) ”
.

Definition anti_shuffle_partial_solve_wit_17_pure_split_goal_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (ch_addr_v: Z) (PreH1 : (ch_addr_v <= INT_MAX)) (PreH2 : (first <= INT_MAX)) (PreH3 : (cur_len <= INT_MAX)) (PreH4 : (out_len <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (ch_addr_v >= INT_MIN)) (PreH7 : (first >= INT_MIN)) (PreH8 : (cur_len >= INT_MIN)) (PreH9 : (out_len >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (0 <= ((string_length (str_l)) + 1 ))) (PreH12 : (0 <= (out_len + 1 ))) (PreH13 : (n = (string_length (str_l)))) (PreH14 : (out <> 0)) (PreH15 : (cur <> 0)) (PreH16 : (out_len = n)) (PreH17 : (cur_len = 0)) (PreH18 : (first = 0)) (PreH19 : ((Zlength (out_l)) = out_len)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_86_pre_z str_l )) (PreH23 : (problem_86_spec_z str_l out_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
|--
  “ (0 < (n + 1 )) ”
.

Definition anti_shuffle_partial_solve_wit_17_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (out_l: (@list Z)) (n: Z) (out: Z) (cur: Z) (out_len: Z) (cur_len: Z) (first: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (cur <> 0)) (PreH4 : (out_len = n)) (PreH5 : (cur_len = 0)) (PreH6 : (first = 0)) (PreH7 : ((Zlength (out_l)) = out_len)) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_86_pre_z str_l )) (PreH11 : (problem_86_spec_z str_l out_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (store_string s_pre str_l )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full cur (n + 1 ) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 < (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (out_len + 1 )) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out_len = n) ” 
  &&  “ (cur_len = 0) ” 
  &&  “ (first = 0) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_86_pre_z str_l ) ” 
  &&  “ (problem_86_spec_z str_l out_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.undef_full cur (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
.

Definition anti_shuffle_partial_solve_wit_17 := anti_shuffle_partial_solve_wit_17_pure -> anti_shuffle_partial_solve_wit_17_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_anti_shuffle_safety_wit_1 : anti_shuffle_safety_wit_1.
Axiom proof_of_anti_shuffle_safety_wit_2 : anti_shuffle_safety_wit_2.
Axiom proof_of_anti_shuffle_safety_wit_3 : anti_shuffle_safety_wit_3.
Axiom proof_of_anti_shuffle_safety_wit_4 : anti_shuffle_safety_wit_4.
Axiom proof_of_anti_shuffle_safety_wit_5 : anti_shuffle_safety_wit_5.
Axiom proof_of_anti_shuffle_safety_wit_6 : anti_shuffle_safety_wit_6.
Axiom proof_of_anti_shuffle_safety_wit_7 : anti_shuffle_safety_wit_7.
Axiom proof_of_anti_shuffle_safety_wit_8 : anti_shuffle_safety_wit_8.
Axiom proof_of_anti_shuffle_safety_wit_9 : anti_shuffle_safety_wit_9.
Axiom proof_of_anti_shuffle_safety_wit_10 : anti_shuffle_safety_wit_10.
Axiom proof_of_anti_shuffle_safety_wit_11 : anti_shuffle_safety_wit_11.
Axiom proof_of_anti_shuffle_safety_wit_12 : anti_shuffle_safety_wit_12.
Axiom proof_of_anti_shuffle_safety_wit_13 : anti_shuffle_safety_wit_13.
Axiom proof_of_anti_shuffle_safety_wit_14 : anti_shuffle_safety_wit_14.
Axiom proof_of_anti_shuffle_safety_wit_15 : anti_shuffle_safety_wit_15.
Axiom proof_of_anti_shuffle_safety_wit_16 : anti_shuffle_safety_wit_16.
Axiom proof_of_anti_shuffle_safety_wit_17 : anti_shuffle_safety_wit_17.
Axiom proof_of_anti_shuffle_safety_wit_18 : anti_shuffle_safety_wit_18.
Axiom proof_of_anti_shuffle_safety_wit_19 : anti_shuffle_safety_wit_19.
Axiom proof_of_anti_shuffle_safety_wit_20 : anti_shuffle_safety_wit_20.
Axiom proof_of_anti_shuffle_safety_wit_21 : anti_shuffle_safety_wit_21.
Axiom proof_of_anti_shuffle_safety_wit_22 : anti_shuffle_safety_wit_22.
Axiom proof_of_anti_shuffle_safety_wit_23 : anti_shuffle_safety_wit_23.
Axiom proof_of_anti_shuffle_safety_wit_24 : anti_shuffle_safety_wit_24.
Axiom proof_of_anti_shuffle_safety_wit_25 : anti_shuffle_safety_wit_25.
Axiom proof_of_anti_shuffle_safety_wit_26 : anti_shuffle_safety_wit_26.
Axiom proof_of_anti_shuffle_safety_wit_27 : anti_shuffle_safety_wit_27.
Axiom proof_of_anti_shuffle_safety_wit_28 : anti_shuffle_safety_wit_28.
Axiom proof_of_anti_shuffle_safety_wit_29 : anti_shuffle_safety_wit_29.
Axiom proof_of_anti_shuffle_safety_wit_30 : anti_shuffle_safety_wit_30.
Axiom proof_of_anti_shuffle_safety_wit_31 : anti_shuffle_safety_wit_31.
Axiom proof_of_anti_shuffle_safety_wit_32 : anti_shuffle_safety_wit_32.
Axiom proof_of_anti_shuffle_safety_wit_33 : anti_shuffle_safety_wit_33.
Axiom proof_of_anti_shuffle_safety_wit_34 : anti_shuffle_safety_wit_34.
Axiom proof_of_anti_shuffle_safety_wit_35 : anti_shuffle_safety_wit_35.
Axiom proof_of_anti_shuffle_safety_wit_36 : anti_shuffle_safety_wit_36.
Axiom proof_of_anti_shuffle_safety_wit_37 : anti_shuffle_safety_wit_37.
Axiom proof_of_anti_shuffle_safety_wit_38 : anti_shuffle_safety_wit_38.
Axiom proof_of_anti_shuffle_safety_wit_39 : anti_shuffle_safety_wit_39.
Axiom proof_of_anti_shuffle_safety_wit_40 : anti_shuffle_safety_wit_40.
Axiom proof_of_anti_shuffle_safety_wit_41 : anti_shuffle_safety_wit_41.
Axiom proof_of_anti_shuffle_safety_wit_42 : anti_shuffle_safety_wit_42.
Axiom proof_of_anti_shuffle_safety_wit_43 : anti_shuffle_safety_wit_43.
Axiom proof_of_anti_shuffle_safety_wit_44 : anti_shuffle_safety_wit_44.
Axiom proof_of_anti_shuffle_safety_wit_45 : anti_shuffle_safety_wit_45.
Axiom proof_of_anti_shuffle_safety_wit_46 : anti_shuffle_safety_wit_46.
Axiom proof_of_anti_shuffle_safety_wit_47 : anti_shuffle_safety_wit_47.
Axiom proof_of_anti_shuffle_safety_wit_48 : anti_shuffle_safety_wit_48.
Axiom proof_of_anti_shuffle_safety_wit_49 : anti_shuffle_safety_wit_49.
Axiom proof_of_anti_shuffle_safety_wit_50 : anti_shuffle_safety_wit_50.
Axiom proof_of_anti_shuffle_safety_wit_51 : anti_shuffle_safety_wit_51.
Axiom proof_of_anti_shuffle_safety_wit_52 : anti_shuffle_safety_wit_52.
Axiom proof_of_anti_shuffle_safety_wit_53 : anti_shuffle_safety_wit_53.
Axiom proof_of_anti_shuffle_safety_wit_54 : anti_shuffle_safety_wit_54.
Axiom proof_of_anti_shuffle_safety_wit_55 : anti_shuffle_safety_wit_55.
Axiom proof_of_anti_shuffle_safety_wit_56 : anti_shuffle_safety_wit_56.
Axiom proof_of_anti_shuffle_safety_wit_57 : anti_shuffle_safety_wit_57.
Axiom proof_of_anti_shuffle_safety_wit_58 : anti_shuffle_safety_wit_58.
Axiom proof_of_anti_shuffle_safety_wit_59 : anti_shuffle_safety_wit_59.
Axiom proof_of_anti_shuffle_entail_wit_1 : anti_shuffle_entail_wit_1.
Axiom proof_of_anti_shuffle_entail_wit_2_1 : anti_shuffle_entail_wit_2_1.
Axiom proof_of_anti_shuffle_entail_wit_2_2 : anti_shuffle_entail_wit_2_2.
Axiom proof_of_anti_shuffle_entail_wit_3_1 : anti_shuffle_entail_wit_3_1.
Axiom proof_of_anti_shuffle_entail_wit_3_2 : anti_shuffle_entail_wit_3_2.
Axiom proof_of_anti_shuffle_entail_wit_3_3 : anti_shuffle_entail_wit_3_3.
Axiom proof_of_anti_shuffle_entail_wit_3_4 : anti_shuffle_entail_wit_3_4.
Axiom proof_of_anti_shuffle_entail_wit_4_1 : anti_shuffle_entail_wit_4_1.
Axiom proof_of_anti_shuffle_entail_wit_4_2 : anti_shuffle_entail_wit_4_2.
Axiom proof_of_anti_shuffle_entail_wit_4_3 : anti_shuffle_entail_wit_4_3.
Axiom proof_of_anti_shuffle_entail_wit_4_4 : anti_shuffle_entail_wit_4_4.
Axiom proof_of_anti_shuffle_entail_wit_5_1 : anti_shuffle_entail_wit_5_1.
Axiom proof_of_anti_shuffle_entail_wit_5_2 : anti_shuffle_entail_wit_5_2.
Axiom proof_of_anti_shuffle_entail_wit_6_1 : anti_shuffle_entail_wit_6_1.
Axiom proof_of_anti_shuffle_entail_wit_6_2 : anti_shuffle_entail_wit_6_2.
Axiom proof_of_anti_shuffle_entail_wit_7_1 : anti_shuffle_entail_wit_7_1.
Axiom proof_of_anti_shuffle_entail_wit_7_2 : anti_shuffle_entail_wit_7_2.
Axiom proof_of_anti_shuffle_entail_wit_8_1 : anti_shuffle_entail_wit_8_1.
Axiom proof_of_anti_shuffle_entail_wit_8_2 : anti_shuffle_entail_wit_8_2.
Axiom proof_of_anti_shuffle_entail_wit_9_1 : anti_shuffle_entail_wit_9_1.
Axiom proof_of_anti_shuffle_entail_wit_9_2 : anti_shuffle_entail_wit_9_2.
Axiom proof_of_anti_shuffle_entail_wit_10_1 : anti_shuffle_entail_wit_10_1.
Axiom proof_of_anti_shuffle_entail_wit_10_2 : anti_shuffle_entail_wit_10_2.
Axiom proof_of_anti_shuffle_entail_wit_11_1 : anti_shuffle_entail_wit_11_1.
Axiom proof_of_anti_shuffle_entail_wit_11_2 : anti_shuffle_entail_wit_11_2.
Axiom proof_of_anti_shuffle_entail_wit_12_1 : anti_shuffle_entail_wit_12_1.
Axiom proof_of_anti_shuffle_entail_wit_12_2 : anti_shuffle_entail_wit_12_2.
Axiom proof_of_anti_shuffle_entail_wit_12_3 : anti_shuffle_entail_wit_12_3.
Axiom proof_of_anti_shuffle_entail_wit_12_4 : anti_shuffle_entail_wit_12_4.
Axiom proof_of_anti_shuffle_entail_wit_13_1 : anti_shuffle_entail_wit_13_1.
Axiom proof_of_anti_shuffle_entail_wit_13_2 : anti_shuffle_entail_wit_13_2.
Axiom proof_of_anti_shuffle_entail_wit_13_3 : anti_shuffle_entail_wit_13_3.
Axiom proof_of_anti_shuffle_entail_wit_14_1 : anti_shuffle_entail_wit_14_1.
Axiom proof_of_anti_shuffle_entail_wit_14_2 : anti_shuffle_entail_wit_14_2.
Axiom proof_of_anti_shuffle_entail_wit_15 : anti_shuffle_entail_wit_15.
Axiom proof_of_anti_shuffle_entail_wit_16 : anti_shuffle_entail_wit_16.
Axiom proof_of_anti_shuffle_return_wit_1 : anti_shuffle_return_wit_1.
Axiom proof_of_anti_shuffle_partial_solve_wit_1_pure : anti_shuffle_partial_solve_wit_1_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_1 : anti_shuffle_partial_solve_wit_1.
Axiom proof_of_anti_shuffle_partial_solve_wit_2_pure : anti_shuffle_partial_solve_wit_2_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_2 : anti_shuffle_partial_solve_wit_2.
Axiom proof_of_anti_shuffle_partial_solve_wit_3_pure : anti_shuffle_partial_solve_wit_3_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_3 : anti_shuffle_partial_solve_wit_3.
Axiom proof_of_anti_shuffle_partial_solve_wit_4 : anti_shuffle_partial_solve_wit_4.
Axiom proof_of_anti_shuffle_partial_solve_wit_5 : anti_shuffle_partial_solve_wit_5.
Axiom proof_of_anti_shuffle_partial_solve_wit_6_pure : anti_shuffle_partial_solve_wit_6_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_6 : anti_shuffle_partial_solve_wit_6.
Axiom proof_of_anti_shuffle_partial_solve_wit_7_pure : anti_shuffle_partial_solve_wit_7_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_7 : anti_shuffle_partial_solve_wit_7.
Axiom proof_of_anti_shuffle_partial_solve_wit_8_pure : anti_shuffle_partial_solve_wit_8_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_8 : anti_shuffle_partial_solve_wit_8.
Axiom proof_of_anti_shuffle_partial_solve_wit_9_pure : anti_shuffle_partial_solve_wit_9_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_9 : anti_shuffle_partial_solve_wit_9.
Axiom proof_of_anti_shuffle_partial_solve_wit_10 : anti_shuffle_partial_solve_wit_10.
Axiom proof_of_anti_shuffle_partial_solve_wit_11 : anti_shuffle_partial_solve_wit_11.
Axiom proof_of_anti_shuffle_partial_solve_wit_12 : anti_shuffle_partial_solve_wit_12.
Axiom proof_of_anti_shuffle_partial_solve_wit_13 : anti_shuffle_partial_solve_wit_13.
Axiom proof_of_anti_shuffle_partial_solve_wit_14 : anti_shuffle_partial_solve_wit_14.
Axiom proof_of_anti_shuffle_partial_solve_wit_15 : anti_shuffle_partial_solve_wit_15.
Axiom proof_of_anti_shuffle_partial_solve_wit_16 : anti_shuffle_partial_solve_wit_16.
Axiom proof_of_anti_shuffle_partial_solve_wit_17_pure : anti_shuffle_partial_solve_wit_17_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_17 : anti_shuffle_partial_solve_wit_17.

End VC_Correct.
