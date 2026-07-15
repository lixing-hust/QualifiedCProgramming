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
Require Import coins_17.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function parse_music -----*)

Definition parse_music_safety_wit_1 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_17_pre_z str_l )) (PreH7 : (music_safe_input_17 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition parse_music_safety_wit_2 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_17_pre_z str_l )) (PreH7 : (music_safe_input_17 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_3 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_music_safety_wit_4 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_music_safety_wit_5 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_music_safety_wit_6 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_music_safety_wit_7 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "value" ) )) # Int  |-> 0)
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_music_safety_wit_8 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (cap = (n + 1 ))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l)))) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (0 <= next)) (PreH14 : (next <= 127)) (PreH15 : (0 <= value)) (PreH16 : (value <= 4)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_17_pre_z str_l )) (PreH20 : (music_safe_input_17 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition parse_music_safety_wit_9 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_music_safety_wit_10 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_11 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition parse_music_safety_wit_12 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l)))) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= next)) (PreH16 : (next <= 127)) (PreH17 : (0 <= value)) (PreH18 : (value <= 4)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_17_pre_z str_l )) (PreH22 : (music_safe_input_17 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_music_safety_wit_13 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l)))) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= next)) (PreH16 : (next <= 127)) (PreH17 : (0 <= value)) (PreH18 : (value <= 4)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_17_pre_z str_l )) (PreH22 : (music_safe_input_17 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_14 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((i + 1 ) < n)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_music_safety_wit_15 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((i + 1 ) < n)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_16 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((i + 1 ) >= n)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_music_safety_wit_17 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((i + 1 ) < n)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (124 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 124) ”
.

Definition parse_music_safety_wit_18 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((i + 1 ) >= n)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (124 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 124) ”
.

Definition parse_music_safety_wit_19 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH2 : ((i + 1 ) < n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition parse_music_safety_wit_20 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (2) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition parse_music_safety_wit_21 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (2) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_22 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (2) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition parse_music_safety_wit_23 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (2) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition parse_music_safety_wit_24 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH2 : ((i + 1 ) < n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition parse_music_safety_wit_25 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((i + 1 ) >= n)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition parse_music_safety_wit_26 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition parse_music_safety_wit_27 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_28 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition parse_music_safety_wit_29 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_30 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_music_safety_wit_31 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> (Znth (i + 1 ) (c_string (str_l)) 0))
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_32 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_music_safety_wit_33 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> 0)
  **  ((( &( "value" ) )) # Int  |-> 4)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_34 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l)))) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= next)) (PreH16 : (next <= 127)) (PreH17 : (0 <= value)) (PreH18 : (value <= 4)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_17_pre_z str_l )) (PreH22 : (music_safe_input_17 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (music_state_17 str_l i output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_35 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (1) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition parse_music_safety_wit_36 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (1) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_music_safety_wit_37 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (1) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition parse_music_safety_wit_38 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (1) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "value" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition parse_music_entail_wit_1 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ ((retval + 1 ) = (retval + 1 )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l 0 output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg retval_3 0 0 output_l )
  **  (IntArray.undef_seg retval_3 0 (retval + 1 ) )
) \/
(
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (music_state_17 str_l 0 (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition parse_music_entail_wit_1_split_goal_1 := 
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (music_state_17 str_l 0 (@nil Z) ) ”
.

Definition parse_music_entail_wit_1_split_goal_2 := 
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition parse_music_entail_wit_1_split_goal_3 := 
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (problem_17_pre_z str_l )) (PreH8 : (music_safe_input_17 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition parse_music_entail_wit_2 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l_2)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l_2 )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l (i + 1 ) output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
) \/
(
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l_2)))) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= next)) (PreH16 : (next <= 127)) (PreH17 : (0 <= value)) (PreH18 : (value <= 4)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_17_pre_z str_l )) (PreH22 : (music_safe_input_17 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 1 ) output_l_2 ) ”
  &&  emp
).

Definition parse_music_entail_wit_2_split_goal_1 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l_2)))) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= next)) (PreH16 : (next <= 127)) (PreH17 : (0 <= value)) (PreH18 : (value <= 4)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_17_pre_z str_l )) (PreH22 : (music_safe_input_17 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 1 ) output_l_2 ) ”
.

Definition parse_music_entail_wit_3 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l_2) ((cons (2) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 2 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_l))) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 111) ” 
  &&  “ ((Znth (i + 1 ) (c_string (str_l)) 0) = 124) ” 
  &&  “ (2 = 2) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l (i + 2 ) output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 (out_size + 1 ) output_l )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
) \/
(
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 2 ) (app (output_l_2) ((cons (2) ((@nil Z))))) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (2) ((@nil Z)))))))) ”
  &&  emp
).

Definition parse_music_entail_wit_3_split_goal_1 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 2 ) (app (output_l_2) ((cons (2) ((@nil Z))))) ) ”
.

Definition parse_music_entail_wit_3_split_goal_2 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (2) ((@nil Z)))))))) ”
.

Definition parse_music_entail_wit_4_1 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l_2 )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l_2) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_l))) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 111) ” 
  &&  “ (0 <> 124) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (4 = 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l (i + 1 ) output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 (out_size + 1 ) output_l )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
) \/
(
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 1 ) (app (output_l_2) ((cons (4) ((@nil Z))))) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (4) ((@nil Z)))))))) ”
  &&  emp
).

Definition parse_music_entail_wit_4_1_split_goal_1 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 1 ) (app (output_l_2) ((cons (4) ((@nil Z))))) ) ”
.

Definition parse_music_entail_wit_4_1_split_goal_2 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((i + 1 ) >= n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (4) ((@nil Z)))))))) ”
.

Definition parse_music_entail_wit_4_2 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l_2) ((cons (4) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_l))) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 111) ” 
  &&  “ ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124) ” 
  &&  “ (0 <= (Znth (i + 1 ) (c_string (str_l)) 0)) ” 
  &&  “ ((Znth (i + 1 ) (c_string (str_l)) 0) <= 127) ” 
  &&  “ (4 = 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l (i + 1 ) output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 (out_size + 1 ) output_l )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
) \/
(
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 1 ) (app (output_l_2) ((cons (4) ((@nil Z))))) ) ” 
  &&  “ ((Znth (i + 1 ) (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth (i + 1 ) (c_string (str_l)) 0)) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (4) ((@nil Z)))))))) ”
  &&  emp
).

Definition parse_music_entail_wit_4_2_split_goal_1 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 1 ) (app (output_l_2) ((cons (4) ((@nil Z))))) ) ”
.

Definition parse_music_entail_wit_4_2_split_goal_2 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ ((Znth (i + 1 ) (c_string (str_l)) 0) <= 127) ”
.

Definition parse_music_entail_wit_4_2_split_goal_3 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (0 <= (Znth (i + 1 ) (c_string (str_l)) 0)) ”
.

Definition parse_music_entail_wit_4_2_split_goal_4 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH3 : ((i + 1 ) < n)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (out_size = (Zlength (output_l_2)))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= next)) (PreH19 : (next <= 127)) (PreH20 : (0 <= value)) (PreH21 : (value <= 4)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (problem_17_pre_z str_l )) (PreH25 : (music_safe_input_17 str_l )) (PreH26 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH27 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (4) ((@nil Z)))))))) ”
.

Definition parse_music_entail_wit_5 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l_2 )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l_2) ((cons (1) ((@nil Z))))) )
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 2 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_l))) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 46) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (1 = 1) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l (i + 2 ) output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 (out_size + 1 ) output_l )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
) \/
(
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 2 ) (app (output_l_2) ((cons (1) ((@nil Z))))) ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 46) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (1) ((@nil Z)))))))) ” 
  &&  “ ((i + 2 ) <= n) ”
  &&  emp
).

Definition parse_music_entail_wit_5_split_goal_1 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ (music_state_17 str_l (i + 2 ) (app (output_l_2) ((cons (1) ((@nil Z))))) ) ”
.

Definition parse_music_entail_wit_5_split_goal_2 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) = 46) ”
.

Definition parse_music_entail_wit_5_split_goal_3 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (1) ((@nil Z)))))))) ”
.

Definition parse_music_entail_wit_5_split_goal_4 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l_2 )) ,
  TT && emp 
|--
  “ ((i + 2 ) <= n) ”
.

Definition parse_music_entail_wit_6_1 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (next: Z) (value: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_l_2)))) (PreH10 : (ch = 32)) (PreH11 : (0 <= next)) (PreH12 : (next <= 127)) (PreH13 : (0 <= value)) (PreH14 : (value <= 4)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (problem_17_pre_z str_l )) (PreH18 : (music_safe_input_17 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (music_state_17 str_l i output_l_2 )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_music_entail_wit_6_2 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (next: Z) (value: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_l_2)))) (PreH10 : (ch = 111)) (PreH11 : (next = 124)) (PreH12 : (value = 2)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (problem_17_pre_z str_l )) (PreH16 : (music_safe_input_17 str_l )) (PreH17 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH18 : (music_state_17 str_l i output_l_2 )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_music_entail_wit_6_3 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (next: Z) (value: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_l_2)))) (PreH10 : (ch = 111)) (PreH11 : (next <> 124)) (PreH12 : (0 <= next)) (PreH13 : (next <= 127)) (PreH14 : (value = 4)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (problem_17_pre_z str_l )) (PreH18 : (music_safe_input_17 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (music_state_17 str_l i output_l_2 )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_music_entail_wit_6_4 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (next: Z) (value: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (1 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_l_2)))) (PreH10 : (ch = 46)) (PreH11 : (0 <= next)) (PreH12 : (next <= 127)) (PreH13 : (value = 1)) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (problem_17_pre_z str_l )) (PreH17 : (music_safe_input_17 str_l )) (PreH18 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH19 : (music_state_17 str_l i output_l_2 )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_music_entail_wit_7 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (cap = (n + 1 ))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l)))) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (0 <= next)) (PreH14 : (next <= 127)) (PreH15 : (0 <= value)) (PreH16 : (value <= 4)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (problem_17_pre_z str_l )) (PreH20 : (music_safe_input_17 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (music_state_17 str_l i output_l )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_size = (Zlength ((music_output_17 (str_l))))) ” 
  &&  “ ((Zlength ((music_output_17 (str_l)))) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (problem_17_spec_z str_l (music_output_17 (str_l)) ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.seg data 0 out_size (music_output_17 (str_l)) )
  **  (IntArray.undef_seg data out_size cap )
) \/
(
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  TT && emp 
|--
  “ (problem_17_spec_z str_l (music_output_17 (str_l)) ) ” 
  &&  “ ((Zlength ((music_output_17 (str_l)))) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (out_size = (Zlength ((music_output_17 (str_l))))) ” 
  &&  “ (output_l = (music_output_17 (str_l))) ”
  &&  emp
).

Definition parse_music_entail_wit_7_split_goal_1 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  TT && emp 
|--
  “ (problem_17_spec_z str_l (music_output_17 (str_l)) ) ”
.

Definition parse_music_entail_wit_7_split_goal_2 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  TT && emp 
|--
  “ ((Zlength ((music_output_17 (str_l)))) <= ((string_length (str_l)) + 1 )) ”
.

Definition parse_music_entail_wit_7_split_goal_3 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  TT && emp 
|--
  “ (out_size = (Zlength ((music_output_17 (str_l))))) ”
.

Definition parse_music_entail_wit_7_split_goal_4 := 
forall (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= next)) (PreH15 : (next <= 127)) (PreH16 : (0 <= value)) (PreH17 : (value <= 4)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (problem_17_pre_z str_l )) (PreH21 : (music_safe_input_17 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (music_state_17 str_l i output_l )) ,
  TT && emp 
|--
  “ (output_l = (music_output_17 (str_l))) ”
.

Definition parse_music_return_wit_1 := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (n: Z) (cap: Z) (out: Z) (data_2: Z) (out_size: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (cap = (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (out_size = (Zlength ((music_output_17 (str_l)))))) (PreH6 : ((Zlength ((music_output_17 (str_l)))) <= ((string_length (str_l)) + 1 ))) (PreH7 : (problem_17_spec_z str_l (music_output_17 (str_l)) )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.seg data_2 0 out_size (music_output_17 (str_l)) )
  **  (IntArray.undef_seg data_2 out_size cap )
|--
  EX (output_l: (@list Z))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_l = (music_output_17 (str_l))) ” 
  &&  “ ((Zlength (output_l)) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (problem_17_spec_z str_l output_l ) ”
  &&  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_l)))
  **  (IntArray.seg data 0 (Zlength (output_l)) output_l )
  **  (IntArray.undef_seg data (Zlength (output_l)) ((string_length (str_l)) + 1 ) )
) \/
(
forall (str_l: (@list Z)) (n: Z) (cap: Z) (out: Z) (data_2: Z) (out_size: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (cap = (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (data_2 <> 0)) (PreH6 : (out_size = (Zlength ((music_output_17 (str_l)))))) (PreH7 : ((Zlength ((music_output_17 (str_l)))) <= ((string_length (str_l)) + 1 ))) (PreH8 : (problem_17_spec_z str_l (music_output_17 (str_l)) )) ,
  (IntArray.seg data_2 0 out_size (music_output_17 (str_l)) )
|--
  (IntArray.seg data_2 0 (Zlength ((music_output_17 (str_l)))) (music_output_17 (str_l)) )
).

Definition parse_music_return_wit_1_split_goal_spatial := 
forall (str_l: (@list Z)) (n: Z) (cap: Z) (out: Z) (data_2: Z) (out_size: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (cap = (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (data_2 <> 0)) (PreH6 : (out_size = (Zlength ((music_output_17 (str_l)))))) (PreH7 : ((Zlength ((music_output_17 (str_l)))) <= ((string_length (str_l)) + 1 ))) (PreH8 : (problem_17_spec_z str_l (music_output_17 (str_l)) )) ,
  (IntArray.seg data_2 0 out_size (music_output_17 (str_l)) )
|--
  (IntArray.seg data_2 0 (Zlength ((music_output_17 (str_l)))) (music_output_17 (str_l)) )
.

Definition parse_music_partial_solve_wit_1_pure := 
forall (music_string_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_17_pre_z str_l )) (PreH4 : (music_safe_input_17 str_l )) (PreH5 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
  **  (store_string music_string_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition parse_music_partial_solve_wit_1_aux := 
forall (music_string_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (problem_17_pre_z str_l )) (PreH4 : (music_safe_input_17 str_l )) (PreH5 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (store_string music_string_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (store_string music_string_pre str_l )
.

Definition parse_music_partial_solve_wit_1 := parse_music_partial_solve_wit_1_pure -> parse_music_partial_solve_wit_1_aux.

Definition parse_music_partial_solve_wit_2 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (problem_17_pre_z str_l )) (PreH6 : (music_safe_input_17 str_l )) (PreH7 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  (store_string music_string_pre str_l )
|--
  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition parse_music_partial_solve_wit_3_pure := 
(
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_17_pre_z str_l )) (PreH7 : (music_safe_input_17 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ”
) \/
(
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((retval + 1 ) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((retval + 1 ) >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval = (string_length (str_l)))) (PreH7 : (0 <= ((string_length (str_l)) + 1 ))) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_17_pre_z str_l )) (PreH11 : (music_safe_input_17 str_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition parse_music_partial_solve_wit_3_pure_split_goal_1 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((retval + 1 ) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((retval + 1 ) >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval = (string_length (str_l)))) (PreH7 : (0 <= ((string_length (str_l)) + 1 ))) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (problem_17_pre_z str_l )) (PreH11 : (music_safe_input_17 str_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition parse_music_partial_solve_wit_3_aux := 
forall (music_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (problem_17_pre_z str_l )) (PreH7 : (music_safe_input_17 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition parse_music_partial_solve_wit_3 := parse_music_partial_solve_wit_3_pure -> parse_music_partial_solve_wit_3_aux.

Definition parse_music_partial_solve_wit_4 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (c_string (str_l)) 0) = 124)) (PreH2 : ((i + 1 ) < n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Znth (i + 1 ) (c_string (str_l)) 0) = 124) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 111) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (((data + (out_size * sizeof(INT) ) )) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
.

Definition parse_music_partial_solve_wit_5 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124)) (PreH2 : ((i + 1 ) < n)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= next)) (PreH18 : (next <= 127)) (PreH19 : (0 <= value)) (PreH20 : (value <= 4)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (problem_17_pre_z str_l )) (PreH24 : (music_safe_input_17 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (music_state_17 str_l i output_l )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Znth (i + 1 ) (c_string (str_l)) 0) <> 124) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 111) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (((data + (out_size * sizeof(INT) ) )) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
.

Definition parse_music_partial_solve_wit_6 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((i + 1 ) >= n)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 111)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= next)) (PreH17 : (next <= 127)) (PreH18 : (0 <= value)) (PreH19 : (value <= 4)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (problem_17_pre_z str_l )) (PreH23 : (music_safe_input_17 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (music_state_17 str_l i output_l )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((i + 1 ) >= n) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 111) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (((data + (out_size * sizeof(INT) ) )) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
.

Definition parse_music_partial_solve_wit_7 := 
forall (music_string_pre: Z) (str_l: (@list Z)) (value: Z) (next: Z) (ch: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 111)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l)))) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= next)) (PreH16 : (next <= 127)) (PreH17 : (0 <= value)) (PreH18 : (value <= 4)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (problem_17_pre_z str_l )) (PreH22 : (music_safe_input_17 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (music_state_17 str_l i output_l )) ,
  (store_string music_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 111) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= next) ” 
  &&  “ (next <= 127) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 4) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (problem_17_pre_z str_l ) ” 
  &&  “ (music_safe_input_17 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (music_state_17 str_l i output_l ) ”
  &&  (((data + (out_size * sizeof(INT) ) )) # Int  |->_)
  **  (CharArray.full music_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_parse_music_safety_wit_1 : parse_music_safety_wit_1.
Axiom proof_of_parse_music_safety_wit_2 : parse_music_safety_wit_2.
Axiom proof_of_parse_music_safety_wit_3 : parse_music_safety_wit_3.
Axiom proof_of_parse_music_safety_wit_4 : parse_music_safety_wit_4.
Axiom proof_of_parse_music_safety_wit_5 : parse_music_safety_wit_5.
Axiom proof_of_parse_music_safety_wit_6 : parse_music_safety_wit_6.
Axiom proof_of_parse_music_safety_wit_7 : parse_music_safety_wit_7.
Axiom proof_of_parse_music_safety_wit_8 : parse_music_safety_wit_8.
Axiom proof_of_parse_music_safety_wit_9 : parse_music_safety_wit_9.
Axiom proof_of_parse_music_safety_wit_10 : parse_music_safety_wit_10.
Axiom proof_of_parse_music_safety_wit_11 : parse_music_safety_wit_11.
Axiom proof_of_parse_music_safety_wit_12 : parse_music_safety_wit_12.
Axiom proof_of_parse_music_safety_wit_13 : parse_music_safety_wit_13.
Axiom proof_of_parse_music_safety_wit_14 : parse_music_safety_wit_14.
Axiom proof_of_parse_music_safety_wit_15 : parse_music_safety_wit_15.
Axiom proof_of_parse_music_safety_wit_16 : parse_music_safety_wit_16.
Axiom proof_of_parse_music_safety_wit_17 : parse_music_safety_wit_17.
Axiom proof_of_parse_music_safety_wit_18 : parse_music_safety_wit_18.
Axiom proof_of_parse_music_safety_wit_19 : parse_music_safety_wit_19.
Axiom proof_of_parse_music_safety_wit_20 : parse_music_safety_wit_20.
Axiom proof_of_parse_music_safety_wit_21 : parse_music_safety_wit_21.
Axiom proof_of_parse_music_safety_wit_22 : parse_music_safety_wit_22.
Axiom proof_of_parse_music_safety_wit_23 : parse_music_safety_wit_23.
Axiom proof_of_parse_music_safety_wit_24 : parse_music_safety_wit_24.
Axiom proof_of_parse_music_safety_wit_25 : parse_music_safety_wit_25.
Axiom proof_of_parse_music_safety_wit_26 : parse_music_safety_wit_26.
Axiom proof_of_parse_music_safety_wit_27 : parse_music_safety_wit_27.
Axiom proof_of_parse_music_safety_wit_28 : parse_music_safety_wit_28.
Axiom proof_of_parse_music_safety_wit_29 : parse_music_safety_wit_29.
Axiom proof_of_parse_music_safety_wit_30 : parse_music_safety_wit_30.
Axiom proof_of_parse_music_safety_wit_31 : parse_music_safety_wit_31.
Axiom proof_of_parse_music_safety_wit_32 : parse_music_safety_wit_32.
Axiom proof_of_parse_music_safety_wit_33 : parse_music_safety_wit_33.
Axiom proof_of_parse_music_safety_wit_34 : parse_music_safety_wit_34.
Axiom proof_of_parse_music_safety_wit_35 : parse_music_safety_wit_35.
Axiom proof_of_parse_music_safety_wit_36 : parse_music_safety_wit_36.
Axiom proof_of_parse_music_safety_wit_37 : parse_music_safety_wit_37.
Axiom proof_of_parse_music_safety_wit_38 : parse_music_safety_wit_38.
Axiom proof_of_parse_music_entail_wit_1 : parse_music_entail_wit_1.
Axiom proof_of_parse_music_entail_wit_2 : parse_music_entail_wit_2.
Axiom proof_of_parse_music_entail_wit_3 : parse_music_entail_wit_3.
Axiom proof_of_parse_music_entail_wit_4_1 : parse_music_entail_wit_4_1.
Axiom proof_of_parse_music_entail_wit_4_2 : parse_music_entail_wit_4_2.
Axiom proof_of_parse_music_entail_wit_5 : parse_music_entail_wit_5.
Axiom proof_of_parse_music_entail_wit_6_1 : parse_music_entail_wit_6_1.
Axiom proof_of_parse_music_entail_wit_6_2 : parse_music_entail_wit_6_2.
Axiom proof_of_parse_music_entail_wit_6_3 : parse_music_entail_wit_6_3.
Axiom proof_of_parse_music_entail_wit_6_4 : parse_music_entail_wit_6_4.
Axiom proof_of_parse_music_entail_wit_7 : parse_music_entail_wit_7.
Axiom proof_of_parse_music_return_wit_1 : parse_music_return_wit_1.
Axiom proof_of_parse_music_partial_solve_wit_1_pure : parse_music_partial_solve_wit_1_pure.
Axiom proof_of_parse_music_partial_solve_wit_1 : parse_music_partial_solve_wit_1.
Axiom proof_of_parse_music_partial_solve_wit_2 : parse_music_partial_solve_wit_2.
Axiom proof_of_parse_music_partial_solve_wit_3_pure : parse_music_partial_solve_wit_3_pure.
Axiom proof_of_parse_music_partial_solve_wit_3 : parse_music_partial_solve_wit_3.
Axiom proof_of_parse_music_partial_solve_wit_4 : parse_music_partial_solve_wit_4.
Axiom proof_of_parse_music_partial_solve_wit_5 : parse_music_partial_solve_wit_5.
Axiom proof_of_parse_music_partial_solve_wit_6 : parse_music_partial_solve_wit_6.
Axiom proof_of_parse_music_partial_solve_wit_7 : parse_music_partial_solve_wit_7.

End VC_Correct.
