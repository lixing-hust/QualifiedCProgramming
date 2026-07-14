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
Require Import coins_6.
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

(*----- Function parse_nested_parens -----*)

Definition parse_nested_parens_safety_wit_1 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_depth_input_6 str_l )) (PreH7 : (parse_safe_input_6 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH9 : (problem_6_pre_z str_l )) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition parse_nested_parens_safety_wit_2 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_depth_input_6 str_l )) (PreH7 : (parse_safe_input_6 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH9 : (problem_6_pre_z str_l )) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_nested_parens_safety_wit_3 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  ((( &( "level" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_nested_parens_safety_wit_4 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  ((( &( "max_level" ) )) # Int  |->_)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_nested_parens_safety_wit_5 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  ((( &( "max_level" ) )) # Int  |-> 0)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_nested_parens_safety_wit_6 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "max_level" ) )) # Int  |-> 0)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_nested_parens_safety_wit_7 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "max_level" ) )) # Int  |-> 0)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_nested_parens_safety_wit_8 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (cap = (n + 1 ))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l)))) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : (0 <= max_level)) (PreH14 : (max_level <= i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_paren_depth_input_6 str_l )) (PreH20 : (parse_safe_input_6 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (problem_6_pre_z str_l )) (PreH23 : (parse_state_6 str_l i level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition parse_nested_parens_safety_wit_9 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((level + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level + 1 )) ”
.

Definition parse_nested_parens_safety_wit_10 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_nested_parens_safety_wit_11 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (41 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 41) ”
.

Definition parse_nested_parens_safety_wit_12 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l)))) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : (0 <= max_level)) (PreH16 : (max_level <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_depth_input_6 str_l )) (PreH22 : (parse_safe_input_6 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (problem_6_pre_z str_l )) (PreH25 : (parse_state_6 str_l i level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((level - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level - 1 )) ”
.

Definition parse_nested_parens_safety_wit_13 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l)))) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : (0 <= max_level)) (PreH16 : (max_level <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_depth_input_6 str_l )) (PreH22 : (parse_safe_input_6 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (problem_6_pre_z str_l )) (PreH25 : (parse_state_6 str_l i level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_nested_parens_safety_wit_14 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l)))) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : (0 <= max_level)) (PreH16 : (max_level <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_depth_input_6 str_l )) (PreH22 : (parse_safe_input_6 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (problem_6_pre_z str_l )) (PreH25 : (parse_state_6 str_l i level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_nested_parens_safety_wit_15 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (max_level) ((@nil Z))))) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition parse_nested_parens_safety_wit_16 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (max_level) ((@nil Z))))) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition parse_nested_parens_safety_wit_17 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l) ((cons (max_level) ((@nil Z))))) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition parse_nested_parens_safety_wit_18 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 40)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l)))) (PreH11 : (1 <= level)) (PreH12 : (level <= (i + 1 ))) (PreH13 : (1 <= max_level)) (PreH14 : (max_level <= (i + 1 ))) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_paren_depth_input_6 str_l )) (PreH18 : (parse_safe_input_6 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (problem_6_pre_z str_l )) (PreH21 : (parse_state_6 str_l (i + 1 ) level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_nested_parens_safety_wit_19 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 41)) (PreH8 : (1 <= out_size)) (PreH9 : (out_size <= (i + 1 ))) (PreH10 : (out_size = (Zlength (output_l)))) (PreH11 : (level = 0)) (PreH12 : (max_level = 0)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (valid_paren_depth_input_6 str_l )) (PreH16 : (parse_safe_input_6 str_l )) (PreH17 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH18 : (problem_6_pre_z str_l )) (PreH19 : (parse_state_6 str_l (i + 1 ) level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_nested_parens_safety_wit_20 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 41)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l)))) (PreH11 : (0 < level)) (PreH12 : (level <= i)) (PreH13 : (0 <= max_level)) (PreH14 : (max_level <= i)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_paren_depth_input_6 str_l )) (PreH18 : (parse_safe_input_6 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (problem_6_pre_z str_l )) (PreH21 : (parse_state_6 str_l (i + 1 ) level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_nested_parens_safety_wit_21 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 32)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l)))) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : (0 <= max_level)) (PreH14 : (max_level <= i)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_paren_depth_input_6 str_l )) (PreH18 : (parse_safe_input_6 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (problem_6_pre_z str_l )) (PreH21 : (parse_state_6 str_l (i + 1 ) level max_level output_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition parse_nested_parens_entail_wit_1 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  (IntArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l 0 0 0 output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg retval_3 0 0 output_l )
  **  (IntArray.undef_seg retval_3 0 (retval + 1 ) )
) \/
(
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l 0 0 0 (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition parse_nested_parens_entail_wit_1_split_goal_1 := 
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l 0 0 0 (@nil Z) ) ”
.

Definition parse_nested_parens_entail_wit_1_split_goal_2 := 
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  TT && emp 
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition parse_nested_parens_entail_wit_1_split_goal_3 := 
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_depth_input_6 str_l )) (PreH8 : (parse_safe_input_6 str_l )) (PreH9 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH10 : (problem_6_pre_z str_l )) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition parse_nested_parens_entail_wit_2_1 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((level + 1 ) <= max_level)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l_2)))) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : (0 <= max_level)) (PreH16 : (max_level <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_depth_input_6 str_l )) (PreH22 : (parse_safe_input_6 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (problem_6_pre_z str_l )) (PreH25 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 40) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (1 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (1 <= max_level) ” 
  &&  “ (max_level <= (i + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) (level + 1 ) max_level output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level + 1 ) <= max_level)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level + 1 ) max_level output_l_2 ) ”
  &&  emp
).

Definition parse_nested_parens_entail_wit_2_1_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level + 1 ) <= max_level)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level + 1 ) max_level output_l_2 ) ”
.

Definition parse_nested_parens_entail_wit_2_2 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((level + 1 ) > max_level)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l_2)))) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : (0 <= max_level)) (PreH16 : (max_level <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_depth_input_6 str_l )) (PreH22 : (parse_safe_input_6 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (problem_6_pre_z str_l )) (PreH25 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 40) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (1 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (1 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) (level + 1 ) (level + 1 ) output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level + 1 ) > max_level)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level + 1 ) (level + 1 ) output_l_2 ) ”
  &&  emp
).

Definition parse_nested_parens_entail_wit_2_2_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level + 1 ) > max_level)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level + 1 ) (level + 1 ) output_l_2 ) ”
.

Definition parse_nested_parens_entail_wit_3 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  (IntArray.seg data 0 (out_size + 1 ) (app (output_l_2) ((cons (max_level) ((@nil Z))))) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ (1 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_l))) ” 
  &&  “ ((level - 1 ) = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) (level - 1 ) 0 output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 (out_size + 1 ) output_l )
  **  (IntArray.undef_seg data (out_size + 1 ) cap )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level - 1 ) 0 (app (output_l_2) ((cons (max_level) ((@nil Z))))) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (max_level) ((@nil Z)))))))) ”
  &&  emp
).

Definition parse_nested_parens_entail_wit_3_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level - 1 ) 0 (app (output_l_2) ((cons (max_level) ((@nil Z))))) ) ”
.

Definition parse_nested_parens_entail_wit_3_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ ((out_size + 1 ) = (Zlength ((app (output_l_2) ((cons (max_level) ((@nil Z)))))))) ”
.

Definition parse_nested_parens_entail_wit_4 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) <> 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 < (level - 1 )) ” 
  &&  “ ((level - 1 ) <= i) ” 
  &&  “ (0 <= max_level) ” 
  &&  “ (max_level <= i) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) (level - 1 ) max_level output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level - 1 ) max_level output_l_2 ) ” 
  &&  “ (0 < (level - 1 )) ”
  &&  emp
).

Definition parse_nested_parens_entail_wit_4_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) (level - 1 ) max_level output_l_2 ) ”
.

Definition parse_nested_parens_entail_wit_4_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (cap = (n + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_l_2)))) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : (0 <= max_level)) (PreH18 : (max_level <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_depth_input_6 str_l )) (PreH24 : (parse_safe_input_6 str_l )) (PreH25 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH26 : (problem_6_pre_z str_l )) (PreH27 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (0 < (level - 1 )) ”
.

Definition parse_nested_parens_entail_wit_5 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (cap = (n + 1 ))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_l_2)))) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : (0 <= max_level)) (PreH16 : (max_level <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_depth_input_6 str_l )) (PreH22 : (parse_safe_input_6 str_l )) (PreH23 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH24 : (problem_6_pre_z str_l )) (PreH25 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (0 <= max_level) ” 
  &&  “ (max_level <= i) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) level max_level output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) level max_level output_l_2 ) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ”
  &&  emp
).

Definition parse_nested_parens_entail_wit_5_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (parse_state_6 str_l (i + 1 ) level max_level output_l_2 ) ”
.

Definition parse_nested_parens_entail_wit_5_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l_2)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ ((Znth i (c_string (str_l)) 0) = 32) ”
.

Definition parse_nested_parens_entail_wit_6_1 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 40)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l_2)))) (PreH11 : (1 <= level)) (PreH12 : (level <= (i + 1 ))) (PreH13 : (1 <= max_level)) (PreH14 : (max_level <= (i + 1 ))) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_paren_depth_input_6 str_l )) (PreH18 : (parse_safe_input_6 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (problem_6_pre_z str_l )) (PreH21 : (parse_state_6 str_l (i + 1 ) level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (0 <= max_level) ” 
  &&  “ (max_level <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) level max_level output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_nested_parens_entail_wit_6_2 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 41)) (PreH8 : (1 <= out_size)) (PreH9 : (out_size <= (i + 1 ))) (PreH10 : (out_size = (Zlength (output_l_2)))) (PreH11 : (level = 0)) (PreH12 : (max_level = 0)) (PreH13 : (valid_string str_l )) (PreH14 : (all_ascii str_l )) (PreH15 : (valid_paren_depth_input_6 str_l )) (PreH16 : (parse_safe_input_6 str_l )) (PreH17 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH18 : (problem_6_pre_z str_l )) (PreH19 : (parse_state_6 str_l (i + 1 ) level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (0 <= max_level) ” 
  &&  “ (max_level <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) level max_level output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_nested_parens_entail_wit_6_3 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 41)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l_2)))) (PreH11 : (0 < level)) (PreH12 : (level <= i)) (PreH13 : (0 <= max_level)) (PreH14 : (max_level <= i)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_paren_depth_input_6 str_l )) (PreH18 : (parse_safe_input_6 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (problem_6_pre_z str_l )) (PreH21 : (parse_state_6 str_l (i + 1 ) level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (0 <= max_level) ” 
  &&  “ (max_level <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) level max_level output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_nested_parens_entail_wit_6_4 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (cap: Z) (out: Z) (data: Z) (ch: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (cap = (n + 1 ))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (ch = 32)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l_2)))) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : (0 <= max_level)) (PreH14 : (max_level <= i)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_paren_depth_input_6 str_l )) (PreH18 : (parse_safe_input_6 str_l )) (PreH19 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH20 : (problem_6_pre_z str_l )) (PreH21 : (parse_state_6 str_l (i + 1 ) level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (0 <= max_level) ” 
  &&  “ (max_level <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l (i + 1 ) level max_level output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_nested_parens_entail_wit_7 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (cap = (n + 1 ))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_l_2)))) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : (0 <= max_level)) (PreH14 : (max_level <= i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_paren_depth_input_6 str_l )) (PreH20 : (parse_safe_input_6 str_l )) (PreH21 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH22 : (problem_6_pre_z str_l )) (PreH23 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (level = 0) ” 
  &&  “ (max_level = 0) ” 
  &&  “ (output_l = (parse_output_6 (str_l))) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (problem_6_spec_z str_l output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
) \/
(
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l_2)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (problem_6_spec_z str_l (parse_output_6 (str_l)) ) ” 
  &&  “ (max_level = 0) ” 
  &&  “ (level = 0) ” 
  &&  “ (out_size = (Zlength ((parse_output_6 (str_l))))) ” 
  &&  “ (output_l_2 = (parse_output_6 (str_l))) ”
  &&  emp
).

Definition parse_nested_parens_entail_wit_7_split_goal_1 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l_2)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (problem_6_spec_z str_l (parse_output_6 (str_l)) ) ”
.

Definition parse_nested_parens_entail_wit_7_split_goal_2 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l_2)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (max_level = 0) ”
.

Definition parse_nested_parens_entail_wit_7_split_goal_3 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l_2)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (level = 0) ”
.

Definition parse_nested_parens_entail_wit_7_split_goal_4 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l_2)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (out_size = (Zlength ((parse_output_6 (str_l))))) ”
.

Definition parse_nested_parens_entail_wit_7_split_goal_5 := 
forall (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (cap = (n + 1 ))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_l_2)))) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : (0 <= max_level)) (PreH15 : (max_level <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_depth_input_6 str_l )) (PreH21 : (parse_safe_input_6 str_l )) (PreH22 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH23 : (problem_6_pre_z str_l )) (PreH24 : (parse_state_6 str_l i level max_level output_l_2 )) ,
  TT && emp 
|--
  “ (output_l_2 = (parse_output_6 (str_l))) ”
.

Definition parse_nested_parens_entail_wit_8 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (n: Z) (cap: Z) (out: Z) (data: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (cap = (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (out_size = (Zlength (output_l_2)))) (PreH6 : (out_size <= n)) (PreH7 : (level = 0)) (PreH8 : (max_level = 0)) (PreH9 : (output_l_2 = (parse_output_6 (str_l)))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_paren_depth_input_6 str_l )) (PreH13 : (parse_safe_input_6 str_l )) (PreH14 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH15 : (problem_6_pre_z str_l )) (PreH16 : (problem_6_spec_z str_l output_l_2 )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.seg data 0 out_size output_l_2 )
  **  (IntArray.undef_seg data out_size cap )
|--
  EX (output_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (out_size = (Zlength (output_l))) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (level = 0) ” 
  &&  “ (max_level = 0) ” 
  &&  “ (output_l = (parse_output_6 (str_l))) ” 
  &&  “ (problem_6_spec_z str_l output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
.

Definition parse_nested_parens_return_wit_1 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_l_2: (@list Z)) (n: Z) (cap: Z) (out: Z) (data_2: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (cap = (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (out_size = (Zlength (output_l_2)))) (PreH6 : (out_size <= n)) (PreH7 : (level = 0)) (PreH8 : (max_level = 0)) (PreH9 : (output_l_2 = (parse_output_6 (str_l)))) (PreH10 : (problem_6_spec_z str_l output_l_2 )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.seg data_2 0 out_size output_l_2 )
  **  (IntArray.undef_seg data_2 out_size cap )
|--
  EX (output_l: (@list Z))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_l = (parse_output_6 (str_l))) ” 
  &&  “ ((Zlength (output_l)) <= (string_length (str_l))) ” 
  &&  “ (problem_6_spec_z str_l output_l ) ”
  &&  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_l)))
  **  (IntArray.seg data 0 (Zlength (output_l)) output_l )
  **  (IntArray.undef_seg data (Zlength (output_l)) ((string_length (str_l)) + 1 ) )
) \/
(
forall (str_l: (@list Z)) (output_l_2: (@list Z)) (n: Z) (cap: Z) (out: Z) (data_2: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (cap = (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (data_2 <> 0)) (PreH6 : (out_size = (Zlength (output_l_2)))) (PreH7 : (out_size <= n)) (PreH8 : (level = 0)) (PreH9 : (max_level = 0)) (PreH10 : (output_l_2 = (parse_output_6 (str_l)))) (PreH11 : (problem_6_spec_z str_l output_l_2 )) ,
  (IntArray.seg data_2 0 out_size output_l_2 )
|--
  (IntArray.seg data_2 0 (Zlength ((parse_output_6 (str_l)))) (parse_output_6 (str_l)) )
).

Definition parse_nested_parens_return_wit_1_split_goal_spatial := 
forall (str_l: (@list Z)) (output_l_2: (@list Z)) (n: Z) (cap: Z) (out: Z) (data_2: Z) (out_size: Z) (level: Z) (max_level: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (cap = (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (data_2 <> 0)) (PreH6 : (out_size = (Zlength (output_l_2)))) (PreH7 : (out_size <= n)) (PreH8 : (level = 0)) (PreH9 : (max_level = 0)) (PreH10 : (output_l_2 = (parse_output_6 (str_l)))) (PreH11 : (problem_6_spec_z str_l output_l_2 )) ,
  (IntArray.seg data_2 0 out_size output_l_2 )
|--
  (IntArray.seg data_2 0 (Zlength ((parse_output_6 (str_l)))) (parse_output_6 (str_l)) )
.

Definition parse_nested_parens_partial_solve_wit_1_pure := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_paren_depth_input_6 str_l )) (PreH4 : (parse_safe_input_6 str_l )) (PreH5 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH6 : (problem_6_pre_z str_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  (store_string paren_string_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition parse_nested_parens_partial_solve_wit_1_aux := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_paren_depth_input_6 str_l )) (PreH4 : (parse_safe_input_6 str_l )) (PreH5 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH6 : (problem_6_pre_z str_l )) ,
  (store_string paren_string_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ”
  &&  (store_string paren_string_pre str_l )
.

Definition parse_nested_parens_partial_solve_wit_1 := parse_nested_parens_partial_solve_wit_1_pure -> parse_nested_parens_partial_solve_wit_1_aux.

Definition parse_nested_parens_partial_solve_wit_2 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_paren_depth_input_6 str_l )) (PreH6 : (parse_safe_input_6 str_l )) (PreH7 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH8 : (problem_6_pre_z str_l )) ,
  (store_string paren_string_pre str_l )
|--
  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ”
  &&  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition parse_nested_parens_partial_solve_wit_3_pure := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_depth_input_6 str_l )) (PreH7 : (parse_safe_input_6 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH9 : (problem_6_pre_z str_l )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ”
) \/
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((retval + 1 ) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((retval + 1 ) >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval = (string_length (str_l)))) (PreH7 : (0 <= ((string_length (str_l)) + 1 ))) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (valid_paren_depth_input_6 str_l )) (PreH11 : (parse_safe_input_6 str_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH13 : (problem_6_pre_z str_l )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition parse_nested_parens_partial_solve_wit_3_pure_split_goal_1 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((retval + 1 ) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((retval + 1 ) >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval = (string_length (str_l)))) (PreH7 : (0 <= ((string_length (str_l)) + 1 ))) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (valid_paren_depth_input_6 str_l )) (PreH11 : (parse_safe_input_6 str_l )) (PreH12 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH13 : (problem_6_pre_z str_l )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition parse_nested_parens_partial_solve_wit_3_aux := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_depth_input_6 str_l )) (PreH7 : (parse_safe_input_6 str_l )) (PreH8 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH9 : (problem_6_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition parse_nested_parens_partial_solve_wit_3 := parse_nested_parens_partial_solve_wit_3_pure -> parse_nested_parens_partial_solve_wit_3_aux.

Definition parse_nested_parens_partial_solve_wit_4 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (ch: Z) (max_level: Z) (level: Z) (output_l: (@list Z)) (out_size: Z) (data: Z) (out: Z) (cap: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (cap = (n + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_l)))) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : (0 <= max_level)) (PreH17 : (max_level <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_depth_input_6 str_l )) (PreH23 : (parse_safe_input_6 str_l )) (PreH24 : (((string_length (str_l)) + 1 ) < INT_MAX)) (PreH25 : (problem_6_pre_z str_l )) (PreH26 : (parse_state_6 str_l i level max_level output_l )) ,
  (store_string paren_string_pre str_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.seg data 0 out_size output_l )
  **  (IntArray.undef_seg data out_size cap )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((level - 1 ) = 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 40) ” 
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (0 <= max_level) ” 
  &&  “ (max_level <= i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_depth_input_6 str_l ) ” 
  &&  “ (parse_safe_input_6 str_l ) ” 
  &&  “ (((string_length (str_l)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_6_pre_z str_l ) ” 
  &&  “ (parse_state_6 str_l i level max_level output_l ) ”
  &&  (((data + (out_size * sizeof(INT) ) )) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
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

Axiom proof_of_parse_nested_parens_safety_wit_1 : parse_nested_parens_safety_wit_1.
Axiom proof_of_parse_nested_parens_safety_wit_2 : parse_nested_parens_safety_wit_2.
Axiom proof_of_parse_nested_parens_safety_wit_3 : parse_nested_parens_safety_wit_3.
Axiom proof_of_parse_nested_parens_safety_wit_4 : parse_nested_parens_safety_wit_4.
Axiom proof_of_parse_nested_parens_safety_wit_5 : parse_nested_parens_safety_wit_5.
Axiom proof_of_parse_nested_parens_safety_wit_6 : parse_nested_parens_safety_wit_6.
Axiom proof_of_parse_nested_parens_safety_wit_7 : parse_nested_parens_safety_wit_7.
Axiom proof_of_parse_nested_parens_safety_wit_8 : parse_nested_parens_safety_wit_8.
Axiom proof_of_parse_nested_parens_safety_wit_9 : parse_nested_parens_safety_wit_9.
Axiom proof_of_parse_nested_parens_safety_wit_10 : parse_nested_parens_safety_wit_10.
Axiom proof_of_parse_nested_parens_safety_wit_11 : parse_nested_parens_safety_wit_11.
Axiom proof_of_parse_nested_parens_safety_wit_12 : parse_nested_parens_safety_wit_12.
Axiom proof_of_parse_nested_parens_safety_wit_13 : parse_nested_parens_safety_wit_13.
Axiom proof_of_parse_nested_parens_safety_wit_14 : parse_nested_parens_safety_wit_14.
Axiom proof_of_parse_nested_parens_safety_wit_15 : parse_nested_parens_safety_wit_15.
Axiom proof_of_parse_nested_parens_safety_wit_16 : parse_nested_parens_safety_wit_16.
Axiom proof_of_parse_nested_parens_safety_wit_17 : parse_nested_parens_safety_wit_17.
Axiom proof_of_parse_nested_parens_safety_wit_18 : parse_nested_parens_safety_wit_18.
Axiom proof_of_parse_nested_parens_safety_wit_19 : parse_nested_parens_safety_wit_19.
Axiom proof_of_parse_nested_parens_safety_wit_20 : parse_nested_parens_safety_wit_20.
Axiom proof_of_parse_nested_parens_safety_wit_21 : parse_nested_parens_safety_wit_21.
Axiom proof_of_parse_nested_parens_entail_wit_1 : parse_nested_parens_entail_wit_1.
Axiom proof_of_parse_nested_parens_entail_wit_2_1 : parse_nested_parens_entail_wit_2_1.
Axiom proof_of_parse_nested_parens_entail_wit_2_2 : parse_nested_parens_entail_wit_2_2.
Axiom proof_of_parse_nested_parens_entail_wit_3 : parse_nested_parens_entail_wit_3.
Axiom proof_of_parse_nested_parens_entail_wit_4 : parse_nested_parens_entail_wit_4.
Axiom proof_of_parse_nested_parens_entail_wit_5 : parse_nested_parens_entail_wit_5.
Axiom proof_of_parse_nested_parens_entail_wit_6_1 : parse_nested_parens_entail_wit_6_1.
Axiom proof_of_parse_nested_parens_entail_wit_6_2 : parse_nested_parens_entail_wit_6_2.
Axiom proof_of_parse_nested_parens_entail_wit_6_3 : parse_nested_parens_entail_wit_6_3.
Axiom proof_of_parse_nested_parens_entail_wit_6_4 : parse_nested_parens_entail_wit_6_4.
Axiom proof_of_parse_nested_parens_entail_wit_7 : parse_nested_parens_entail_wit_7.
Axiom proof_of_parse_nested_parens_entail_wit_8 : parse_nested_parens_entail_wit_8.
Axiom proof_of_parse_nested_parens_return_wit_1 : parse_nested_parens_return_wit_1.
Axiom proof_of_parse_nested_parens_partial_solve_wit_1_pure : parse_nested_parens_partial_solve_wit_1_pure.
Axiom proof_of_parse_nested_parens_partial_solve_wit_1 : parse_nested_parens_partial_solve_wit_1.
Axiom proof_of_parse_nested_parens_partial_solve_wit_2 : parse_nested_parens_partial_solve_wit_2.
Axiom proof_of_parse_nested_parens_partial_solve_wit_3_pure : parse_nested_parens_partial_solve_wit_3_pure.
Axiom proof_of_parse_nested_parens_partial_solve_wit_3 : parse_nested_parens_partial_solve_wit_3.
Axiom proof_of_parse_nested_parens_partial_solve_wit_4 : parse_nested_parens_partial_solve_wit_4.

End VC_Correct.
